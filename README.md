# zkboo-hs

[![Build Status](https://img.shields.io/travis/cocreature/zkboo-hs.svg)](https://travis-ci.org/cocreature/zkboo-hs)

A Haskell implementation of the [ZKBoo protocol](https://eprint.iacr.org/2016/163.pdf)
for non-interactive zero-knowledge proofs of boolean circuits.

## Overview of the protocol

ZKBoo generates non-interactive zero-knowledge proofs for circuits
consisting of addition and multiplication. A special case of this are
circuits over ℤ₂, i.e., boolean circuits.

The basic idea behind ZKBoo is to distribute the evaluation of the
circuit over three parties. The commitments of the final views are
sent to the verifier. The verifier then sends the challenge to the
prover which reveals the two views specified by the challenge. To
reduce the soundness error, multiple rounds of this protocol are
executed. The protocol is made non-interactive by applying the
[Fiat-Shamir heuristic](https://en.wikipedia.org/wiki/Fiat%E2%80%93Shamir_heuristic)
which draws the challenges from the hash of the commitments.

## Comparison to QAP-based ZKSNARKs

Advantages
* Proof generation is significantly faster.
* No need for trusted parameter generation.
* Arguably simpler to implement.

Disadvantages
* Significantly larger proof sizes.
* Slightly slower verification.

## Disclaimer

I am not a cryptographer and I only wrote this code for learning purposes.
I do not recommend that you use it for cryptographic applications.
