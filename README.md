# HEAAN and FV in SageMath
The SageMath implementaiton of two homomorphic encryption schemes: [HEAAN](https://eprint.iacr.org/2016/421.pdf) and [FV with polynomial plaintext modulus](https://eprint.iacr.org/2018/785.pdf)(`FV`).
More precisely, two variants of HEAAN are implemented:
- `HEAAN`: the original version from [ePrint 2016/421](https://eprint.iacr.org/2016/421.pdf) that uses sparse secret keys and the "special-modulus" technique for key switching;
- `HEAAN_FV_KS`: a variant without sparse secret keys and with the "bit-decomposition" key switching method (as in FV).

This code is used in the paper "When HEAAN Meets FV: a New Somewhat Homomorphic Encryption with Reduced Memory Overhead" to compute the following functions homomorphically:
- the exponential function (see `exp_test` in the code),
- the sine (see `sine_test`),
- the standard logistic function (see `logist_test`),
- power functions (see `power_test`).
