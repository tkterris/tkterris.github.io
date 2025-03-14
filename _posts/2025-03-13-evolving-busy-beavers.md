---
modified_date: 2025-03-15
---
# Deriving BB(n+1) from BB(n) with O(1) advice bits

## Introduction

In section 5.5 of The Busy Beaver Frontier [^1], Scott Aaronson describes a proof by Chaitin [^2] that, for any universal prefix-free language *L*, *K (BB<sub>L</sub>(n+1) \| BB<sub>L</sub>(n)) = O(log n)*, where *K(A\|B)* is the prefix-free Kolmogorov complexity of *A* given the input string *B*. That is, if you know the *n*'th Busy Beaver, you could determine *BB<sub>L</sub>(n+1)* with *O(log n)* additional bits. At the end of the section, Aaronson poses the following question:

> On the other hand, for bit-based programs, could Theorem 20 be improved to get the number of advice bits below O(log n)—possibly even down to a constant? How interrelated are the successive values of BB(n)?

In this post, I sketch a proof that the required number of advice bits needed to determine *BB<sub>L</sub>(n+1)* from *BB<sub>L</sub>(n)* is indeed a constant, for [almost all](https://mathworld.wolfram.com/AlmostAll.html) *n*. This uses a similar approach to that used in [^1], but instead of incrementally checking lower bounds to Chaitin's constant, we incrementally check a tally of the number of programs of length *n+1* that halt.

---

## Proof

This proof sketch consists of two parts: 
- a description of a method used to determine the number of halting programs of length *n+1* from *BB<sub>L</sub>(n)* with some bits of uncertainty
- a demonstration that the number of advice bits needed to resolve that uncertainty, getting the number of halting programs of length *n+1* and therefore *BB<sub>L</sub>(n+1)*, is a constant for almost all *n*

Note that while the Busy Beaver game envisioned by Radó [^3] involved *n*-state, two-symbol Turing machines, in this post we will be considering the equivalent function for *n*-bit programs in a prefix-free universal language *L* (the choice of language itself doesn't matter; the results are equivalent for Lisp, Zot, Binary Lambda Calculus, or any other such language). So, from here on out, *BB(n)* specifically means *BB<sub>L</sub>(n)*. Also, we're doing computer science today, so every *log* you see is the logarithm base 2, rounded down to the nearest integer.

First, some notation: 
- *log\*(x)* is the [iterated logarithm](https://en.wikipedia.org/wiki/Iterated_logarithm) of *x*.
- *iterLogProduct(x)* is the product of the repeated logarithm of the integer *x* (including *x* itself) until we get 1, then multiplied by *2^log\*(x+1)*, i.e. *x \* log(x) \* log(log(x)) \* ... \* 2 \* 2^log\*(x+1)*. 
- *iterLogSum(x)* is the sum of the repeated logarithm of the integer *x* until we get 1, plus *log\*(x+1)*, i.e. *log(x) + log(log(x)) + log(log(log(x))) + ... + 1 + log\*(x+1)*. Note that *log(iterLogProduct(x))* is equal to *iterLogSum(x)*.
- *enc(x)* returns the (prefix-free) [Elias omega coding](https://en.wikipedia.org/wiki/Elias_omega_coding) of the integer *x*. Note that for any *x*, *len(enc(x)) = iterLogSum(x)*.
- When I say a condition applies for "almost all *n*", I mean it in the sense described [here](https://mathworld.wolfram.com/AlmostAll.html). That is, as *n* increases, the probability that the condition holds asymptotically converges on 1.

### Estimating the number of halting programs of length *n+1*

Consider the following pseudocode:

```
doesThisManyHalt(int n, int p, bitstream stream) {
    int lengthOfBitstream = n - len(doesThisManyHalt.toBinaryString()) - len(enc(n)) - len(enc(p));
    int candidate = stream.readBits(lengthOfBitStream).toInt() * 2 ^ p;
    int halted = 0;
    getAllProgramsOfLength(n + 1).runInParallel().whenHalt(() -> {
        halted++;
        if (halted > candidate) {
            exit;
        }
    });
}
```

Suppose we know *BB(n)*. *doesThisManyHalt* takes a prefix-free coding of *n*, a prefix-free coding of some number *p* of lost bits of precision, and a non-prefix-free bitstream of the binary representation of the candidate value for the number of programs of exactly length *n+1* that halt (with *p* least-significant bits truncated). It consumes enough bits of the bitstream such that the length of the program (*C*) plus its inputs (*len(enc(n))*, *len(enc(p))*, and the candidate's bits) is equal to *n*. This gives us result <span id="result1">__(1)__</span>: *doesThisManyHalt* consumes *n - C - len(enc(n)) - len(enc(p))* candidate bits. It then iterates through each of the *2<sup>n+1</sup>* program strings of length *n+1*, running them in parallel. Whenever one of them halts, it is added to a tally, and if that tally exceeds the input candidate multiplied by *2<sup>p</sup>*, the entire program halts. 

Because this program and its inputs are length *n* and we know *BB(n)*, we can evaluate whether this program halts. So, this can be used in a test to determine the number of halting programs of length *n+1*: repeatedly check if *doesThisManyHalt* halts, incrementing the candidate bitstream if it does. If the bitstream is saturated with 1's, increment the number of lost bits *p* and retry. Eventually we will have found inputs that do not halt, and so we will have computed an estimate of the number of halting programs of length *n+1*. The value *p* of the amount of lost precision is the number of advice bits we need -- once we have those last few bits from an oracle, we will know the exact number of programs of length *n+1* that halt. We can then run all such programs in parallel until that many halt, and we can select the longest-running such program as *BB(n+1)*.

Note that, at first glance, this doesn't get any better results than the procedure described in [^1]. The number of halting programs of length *n+1* is potentially *2<sup>n+1</sup>*, requiring a non-prefix-free bit coding of length *n+1*, meaning that every single one of the bits lost when calling *doesThisManyHalt* will contribute to the imprecision *p*. In particular, since the definition of *doesThisManyHalt* requires some constant *C* bits and *len(enc(n))* is of size *O(log(n))*, we again need *O(log(n)) + C* advice bits to determine *BB(n+1)*.

However, the number of halting prefix-free programs of length *2<sup>n+1</sup>* is much less than *2<sup>n+1</sup>*. In fact, the number of such programs decreases fast enough, relative to *2<sup>n+1</sup>*, that we can fit in *enc(n)*.

### Upper bounds on the number of halting programs

The definition of Chaitin's constant: over all programs *p*, *Ω = sum(2<sup>-\|p\|</sup>) \| p halts*. However, instead of this formulation, consider the function *f(n)* which is the fraction of programs of length *n* that halt, i.e. for each *n* there are *2<sup>n</sup>f(n)* programs of length *n* that halt. Because each halting program of length *n* contributes *2<sup>-n</sup>* to Chaitin's constant, we have *Ω = sum(2<sup>n</sup>f(n)2<sup>-n</sup>) = sum(f(n))* for all *n = 1 → ∞*. This means that *f(n) < n<sup>-1</sup>* for almost all *n*, since the harmonic series diverges and Chaitin's constant does not. The same goes for *f(n) = (n log(n))<sup>-1</sup>* and for *f(n) = (n log(n) log(log(n)))<sup>-1</sup>* and so on. Finally, we can still satisfy the inequality if we multiply by a factor of *2^-log\*(x+1)* (since *log\*(x) < log<sup>m</sup>(x)* for all *m*) and offset the argument for *iterLogProduct* by 1 (resulting in an increase in the infinite sum by a constant). Ultimately, we find that *f(n) < iterLogProduct(n-1)<sup>-1</sup>* for almost all *n*.[^4]

By substituting *iterLogProduct(n-1)<sup>-1</sup>* for *f(n)* in the number of halting programs *2^(n) * f(n)*, we find that the maximum bits required for the candidate of *doesThisManyHalt* is:

```
requiredBits = log(number of halting programs of length n+1) + 1
             = log(2^(n+1) * f(n+1)) + 1
             < log(2^(n+1) * iterLogProduct((n+1)-1)^-1) + 1
             < n + 1 - log(iterLogProduct(n)) + 1
             < n + 2 - iterLogSum(n)
             < n + 2 - len(enc(n))
```

So, the required number of bits to count the number of halting programs of length *n+1* is less than *n + 2 - len(enc(n))*, giving result <span id="result2">__(2)__</span>.

Recall [result (1)](#result1), the number of bits of the candidate is equal to *n - C - len(enc(n)) - len(enc(p))*, where *C* is the constant length of *doesThisManyHalt* (not including input) and *p* is the number of advice bits we will need. The number of advice bits *p* is the required number of bits minus the number of bits in the candidate. So, by substituting [result (1)](#result1) and [result (2)](#result2) for the candidate and required bits, we have:

```
adviceBits = p = requiredBits - candidateBits
             p = requiredBits - (n - C - len(enc(n)) - len(enc(p)))         //from (1)
             p < n + 2 - len(enc(n)) - (n - C - len(enc(n)) - len(enc(p)))  //from (2)
             p < C + 2 + len(enc(p))
```

Which gives result <span id="result3">__(3)__</span>: the number of advice bits *p* is less than *C + 2 + len(enc(p))*. However, this ceiling on the number of advice bits is independent of *n*. So, for almost all *n*, the number of advice bits needed to determine *BB(n+1)* given *BB(n)* is at most a constant. ∎

---

## Discussion

I'm not completely confident in this proof, particularly the hand-waviness around the sum of *iterLogProduct(n-1)<sup>-1</sup>* diverging. That said, it does __feel__ true -- in OEIS sequence [A195691](https://oeis.org/A195691), you can see that [result (2)](#result2) holds: *requiredBits(n+1) < n + 2 - len(enc(n))*. For example, *requiredBits(44) = log(A195691(44)) + 1 = log(104234931) + 1 = 27*, while *(44 - 1) + 2 - len(enc(44 - 1)) = 45 - 12 = 33*. 

An interesting conclusion is that all but a constant number of programs of length *n+1* halt before *BB(n)* -- that is, *doesThisManyHalt* with *n* total bits runs longer than all but the last *2<sup>p</sup>* programs of length *n+1*. So, incrementing *n* only adds a constant number of "interesting" programs (i.e. programs of length *n+1* that run longer than *BB(n)*). This goes against my intuition that things ought to get "exponentially more interesting" as program lengths increase.

It would be worth investigating the occasional cases where [result (2)](#result2) breaks -- while it could theoretically occur infinitely many times (just infinitely less often as *n* increases), I suspect that for any sensible language it never actually happens. Whether this is true, and what exactly "sensible" means, aren't obvious. Perhaps something involving languages that have minimally-sized interpreters?

---

[^1]: Scott Aaronson. 2020. The Busy Beaver Frontier. <https://www.scottaaronson.com/papers/bb.pdf>
[^2]: G. Chaitin. To a mathematical theory of evolution and biological creativity. Technical Report 391, Centre for Discrete Mathematics and Theoretical Computer Science, 2010. <https://www.cs.auckland.ac.nz/research/groups/CDMTCS/researchreports/391greg.pdf>.
[^3]: Radó, Tibor (May 1962). "On non-computable functions". Bell System Technical Journal. 41 (3): 877–884. <https://en.wikipedia.org/wiki/Busy_beaver>
[^4]: To be clear, this doesn't necessarily apply for __all__ *n*, just the vast majority, with probability approaching 1 as *n* tends to infinity. We can easily construct an example where this doesn't hold for a single *n*. Consider the prefix-free language which is defined: 
    - if the first bit is a zero, treat the rest of the stream as input to the interpreter of some other prefix-free language (Lisp etc)
    - if the first bit is a one, read exactly *2⇈20* bits, halting iff the last bit is even
    
    Suppose we knew *BB(2⇈20)*. In this case, the candidate for *doesThisManyHalt* for *BB(n+1)* would be *O(n)* bits long (specifically, *2⇈20* bits). So, we'd need *O(log(n))* advice bits to use *doesThisManyHalt* to determine *BB(n+1)* for this particular value of *n*.

