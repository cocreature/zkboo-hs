# zkboo-hs

A Haskell implementation of the [ZKBoo
protocol](https://eprint.iacr.org/2016/163.pdf) for zero-knowledge
proofs of boolean circuits.

## Comparison to QAP-based ZKSNARKs

Advantages
* Proof generation is significantly faster.
* No need for trusted parameter generation.
* Arguably simpler to implement.

Disadvantages
* Significantly larger proof sizes.
* Slightly slower verification.

## Disclaimer

I am not a cryptographer and I wrote this code only for learning purposes. 
I do not recommend that you use it for cryptographic applications.
