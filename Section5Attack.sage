"""
Implementation of the attack described in the paper:
"Dimensional eROSion: Improving the ROS Attack with Decomposition in Higher Bases".

This script provides a proof-of-concept of the polynomial-time attack described in the paper, specifically tailored to:
- Schnorr blind signatures on the secp256k1 elliptic curve.
- A 256-bit prime field setup (secp256k1 standard parameters).
"""

import hashlib
from sage.modules.free_module_integer import IntegerLattice

# ===========================================================
# Public parameters setup: Curve secp256k1
# ===========================================================

q = 0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffefffffc2f
Zq = GF(q)
E = EllipticCurve(Zq, [0,7])
G = E(0x79be667ef9dcbbac55a06295ce870b07029bfcdb2dce28d959f2815b16f81798, 0x483ada7726a3c4655da4fbfc0e1108a8fd17b448a68554199c47d08ffb10d4b8)
E.set_order(0xfffffffffffffffffffffffffffffffebaaedce6af48a03bbfd25e8cd0364141 * 0x1)
p= G.order()
Zp = GF(p)

# ===========================================================
# Helper functions for Schnorr blind signatures
# ===========================================================

def random_oracle(R,m):
    to_hash=str(G.xy()[0])+str(X.xy()[0])+str(R.xy()[0])+m
    hash=hashlib.sha512(to_hash.encode()).digest()
    return Zp(int.from_bytes(hash,"big"))
 
# Schnorr signature verification
def verify(message, signature):
    R, s = signature
    c = random_oracle(R, message)
    assert G * s == X * c + R, "Invalid Schnorr signature"
    return True

def inner_product(coefficients, values):
    return sum(y * x for x, y in zip(coefficients, values))

def scale_to_Zp(vec):
    assert all(gcd(p, el.denominator()) == 1 for el in vec), "Denominator not invertible mod p"
    return vector(Zp, [Zp(el.numerator()) / Zp(el.denominator()) for el in vec])

# ===========================================================
# Helper functions for operations in multiple bases
# ===========================================================

# Generate powers for the multi-base decomposition
def generate_powers(n=7, group_bit_len=256, extra_digits=2):
    max_number = 2^group_bit_len
    powers = []
    k = n - 1

    while k >= 1:
        # B = 2 * k * log(p,k+1)^(1/k), Theorem 2 Bound (from paper)
        B = 1/500  # Improved Heuristic Value

        max_k = ceil(log(max_number, k + 1))
        if k == 1:
            e_k = 0
        else:
            e_k = ceil(log(B * log(p, k + 1) * p^((k - 1)/k), k + 1)) + extra_digits

        powers = [(k + 1, i) for i in range(e_k, max_k)] + powers
        max_number = (k + 1)^e_k
        k -= 1

    return powers

# Perform multi-base decomposition of integers
def multi_base_decompose(input_number, powers):
    remaining_value = ZZ(input_number)
    digits = []

    for base in powers[::-1]:
        digits = [remaining_value // base] + digits
        remaining_value %= base

    assert inner_product(digits, powers) == input_number, "Incorrect decomposition"
    return digits


# ===========================================================
# Paramter selection for the attack
# ===========================================================

max_basis = 7
extra_digits = 0
factored_powers = generate_powers(n=max_basis + 1, group_bit_len=ceil(log(p, 2)), extra_digits=extra_digits)

powers_bases = [base for base, exp in factored_powers]
powers = [base^exp for base, exp in factored_powers]

ell = len(powers)
e_k = [
    min(factored_powers[i][1] if factored_powers[i][0] == k else 1000 for i in range(ell))
    for k in range(2, max_basis + 2)
]

I_k = [
    min(i if factored_powers[i][0] == k else 1000 for i in range(ell))
    for k in range(2, max_basis + 2)
] + [ell]

# ===========================================================
# Start of interactions with the Server
# ===========================================================

# Server: Generate public/private key pair
x = Zp.random_element()
X = G * x

# Server: Generate Schnorr commitments for each session
r = [Zp.random_element() for _ in range(ell)]
R = [G * r_i for r_i in r]

# Adversary: Prepare messages and blinding factors
messages = [f"message_{i}" for i in range(ell)] + ["forged_message"]
alpha = [[Zp.random_element() for _ in range(powers_bases[i])] for i in range(ell)]
beta = [Zp.random_element() for _ in range(ell)]

# Adversary: Generate blinded commitment points
blinded_R = [
    [R[i] + G * alpha[i][b] + beta[i] * X for b in range(powers_bases[i])]
    for i in range(ell)
]

# Adversary: Query random oracle with blinded points to simulate signatures
c = [
    [random_oracle(blinded_R[i][b], messages[i]) for b in range(powers_bases[i])]
    for i in range(ell)
]

# Adversary: Construct lattices 
queries_diff = [
    [c[i][b] - c[i][0] for b in range(1, powers_bases[i])]
    for i in range(ell)
]

lattices = [
    block_matrix([[Matrix(ZZ, queries_diff[i])], [p * matrix.identity(powers_bases[i] - 1)]])
    for i in range(ell)
]

# Estimate lattice quality using Gram-Schmidt (for reordering)
GSO_lattices = [lattice.gram_schmidt() for lattice in lattices]
lattice_quality = [sum(norm(vec)^2 for vec in GSO) for GSO in GSO_lattices]

# Reorder lattices to improve decomposition success probability
rankings = []
for k in range(max_basis):
    k_quality = lattice_quality[I_k[k]:I_k[k + 1]]
    rankings += [sorted(k_quality).index(q) + I_k[k] for q in k_quality]

messages = [messages[i] for i in rankings] + [messages[-1]]
R = [R[i] for i in rankings]
alpha = [alpha[i] for i in rankings]
beta = [beta[i] for i in rankings]
blinded_R = [blinded_R[i] for i in rankings]
c = [c[i] for i in rankings]
queries_diff = [queries_diff[i] for i in rankings]
lattices = [lattices[i] for i in rankings]

# Solve Closest Vector Problem (CVP) to find lattice approximations
closest_vectors = [
    IntegerLattice(lattices[i]).babai([j * powers[i] for j in range(1, powers_bases[i])])
    for i in range(ell)
]

# Compute normalization factors for lattice approximations
mu = [
    (1 / Zp(powers[i])) * scale_to_Zp(lattices[i].solve_left(closest_vectors[i]))[0]
    for i in range(ell)
]

# ===========================================================
# Decomposition phase: Attempt decomposition of target value
# ===========================================================

MAX_ATTEMPTS = 98
attempts = 0
while True:
    attempts += 1

    # Randomly select a scalar to randomize the target decomposition
    extra_alpha = Zp.random_element()
    
    # Compute forged point using lattice approximations
    R_forge = extra_alpha * inner_product([i * j for i, j in zip(powers, mu)], R)
    c_to_decompose = random_oracle(R_forge, messages[ell])

    # Compute the integer value to decompose using lattice results
    NUM_to_decompose = (
        extra_alpha^(-1) * c_to_decompose
        + sum([powers[i] * mu[i] * (-c[i][0]) for i in range(ell)])
        - inner_product(beta, [powers[i] * mu[i] for i in range(ell)])
    )

    digits = [0] * ell

    # Attempt digit-by-digit decomposition
    for i in range(ell)[::-1]:
        current_digits = multi_base_decompose(NUM_to_decompose, powers)
        
        # If non-zero higher digit appears, decomposition attempt fails
        if i != ell - 1 and current_digits[i + 1] != 0:
            break
        
        new_digit = current_digits[i]
        digits[i] = new_digit
        
        # Ensure the new digit is valid in its base
        if new_digit > powers_bases[i]:
            break
        
        # Update the remaining number by subtracting the approximated digit
        if new_digit != 0:
            NUM_to_decompose -= powers[i] * mu[i] * queries_diff[i][new_digit - 1]
        
        # Negative decomposition is invalid
        if NUM_to_decompose < 0:
            break

    # Successful decomposition found
    if NUM_to_decompose == 0:
        break

    # Limit the number of decomposition attempts
    if attempts > MAX_ATTEMPTS:
        break

# Handle decomposition failure explicitly
if attempts > MAX_ATTEMPTS:
    print("Decomposition failed, need to resample the lattices")

# ===========================================================
# Forgery phase: Produce forged Schnorr signatures
# ===========================================================

else:
    # Adversary sends computed values to the server
    blinded_c = [c[i][digits[i]] + beta[i] for i in range(ell)]
    blinded_c = [blinded_c[rankings.index(i)] for i in range(ell)]

    # Server generates responses based on blinded challenges
    s = [blinded_c[i] * x + r[i] for i in range(ell)]

    # Adversary constructs forged Schnorr signatures
    s = [s[i] for i in rankings]
    
    # Generate valid Schnorr signatures from blinded commitments
    forged_signatures = [
        (blinded_R[i][digits[i]], s[i] + alpha[i][digits[i]])
        for i in range(ell)
    ]
    
    # Include the additional forged signature from lattice solutions
    forged_signatures += [
        (R_forge, extra_alpha * inner_product([i * j for i, j in zip(powers, mu)], s))
    ]

    # Verify correctness of all generated signatures
    valid_sigs = all([
        verify(messages[i], forged_signatures[i])
        for i in range(ell + 1)
    ])

    print(f"All signatures successfully verified: {valid_sigs}")
