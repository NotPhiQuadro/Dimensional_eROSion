# Dimensional_eROSion

This repository contains a SageMath implementation of the attack described in the [paper](https://eprint.iacr.org/2025/306):

> **Dimensional eROSion: Improving the ROS Attack with Decomposition in Higher Bases**

The attack improves upon previous polynomial solutions to the Random Inhomogeneities in an Overdetermined Solvable system (ROS) problem by using decompositions in higher basis. As a concrete application, this script shows how to break the one-more unforgeability of Schnorr blind signatures over the secp256k1 elliptic curve.


## ▶️ Usage

To run the attack, simply open the SageMath environment and execute:

```` bash
sage Section5Attack.sage
````

## 🔒 Disclaimer
This code is provided for educational and research purposes only and should not be used to attack any real-world systems.