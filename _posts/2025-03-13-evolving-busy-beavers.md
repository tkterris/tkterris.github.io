## Deriving BB(n+1) from BB(n) with O(1) advice bits

In section 5.5 of The Busy Beaver Frontier [^1], Scott Aaronson describes a proof by Chaitin [^2] that, for any universal prefix-free language *L*, *K (BB<sub>L</sub>(n + 1) ｜ BB<sub>L</sub>(n)) = O(log n)*, where *K(A｜B)* is the prefix-free Kolmogorov complexity of *A* given the input string *B*. That is, if you know the *n*'th Busy Beaver, you could determine *BB<sub>L</sub>(n+1)* with *O(log n)* additional bits. At the end of the section, Aaronson poses the following question:

> On the other hand, for bit-based programs, could Theorem 20 be improved to get the number of advice bits below O(log n)—possibly even down to a constant? How interrelated are the successive values of BB(n)?

In this post, I sketch a proof that the required number of advice bits will be a constant with a probability approaching 1 as *n* tends to infinity. This won't necessarily be true for all *n* -- see the block-quote aside further down -- but in the worst case, the frequency of such *n* will asymptotically approach zero. This uses a simliar approach to that used in [^1], but instead of incrementally checking lower bounds to Chaitin's constant, we incrementally check a tally of the number of programs of length *n+1* that halt.

---

This proof sketch consists of two parts: 
- a description of the method used to determine the number of halting programs of length *n+1* from *BB<sub>L</sub>(n)* with some uncertainty
- a demonstration that the additional bits needed to isolate the number of halting programs, and therefore *BB<sub>L</sub>(n + 1)*, is almost always a constant.

Note that while the Busy Beaver game envisioned by Radó [^3] involved *n*-state, two-symbol Turing machines, in this paper we will be considering the equivalent function for *n*-bit programs in a prefix-free universal language *L*. The choice of language itself doesn't matter; the results are equivalent for Lisp, Zot, Binary Lambda Calculus, or any other such language.

First, some notation: 
- We're doing computer science today, so every *log* you see is the logarithm base 2.
- *iterLogProduct(x)* is the product of iteratively taking the logarithm of the integer *x* until the result is less than 1, i.e. *log(x) log(log(x)) log(log(log(x))) ...*. 
- *iterLogSum(x)* is the sum of iteratively taking the logarithm of the integer *x* until the result is less than 1 (with the value in the terminating case set to 1), i.e. *log(x) + log(log(x)) + log(log(log(x))) + ... + 1*. *log(iterLogProduct(x)* is equal to *iterLogSum(x)*.
- *enc(x)* returns the prefix-free encoding of the integer *x*, e.g. the Levenshtein coding [^4]. For any *x*, *len(enc(x)) <= iterLogSum(x + 1)*.

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

*doesThisManyHalt* takes a prefix-free coding of the size *n* of the currently-known Busy Beaver, a prefix-free coding of some number *p* of lost bits of precision, and a non-prefix-free bitstream of the binary representation of the candidate value for the number of programs of exactly length *n+1* that halt (with some lost bits of precision). It consumes enough bits of the bitstream such that the length of the program (*C*) plus its inputs (*len(enc(n))*, *len(enc(p))*, and the candidate bits) is equal to *n*, then iterates through each of the *2<sup>n+1</sup>* program strings of length *n+1*, running them in parallel. Whenever one of them halts, it is added to a tally, and if that tally exceeds the input candidate multiplied by *2<sup>p</sup>*, the entire program halts. 

Because this program and its inputs are length *n* and we know *BB(n)*, we can evaluate whether this program halts. So, this can be used in a test to determine the number of halting programs of length *n+1*: repeatedly check if *doesThisManyHalt* halts, incrementing the candidate bitstream if it does. If the bitstream is saturated with 1's, increment the number of lost bits *p* and remove some bits of the candidate, and retry. Eventually we will have found inputs that do not halt, and so we will have computed an estimate of the number of halting programs of length *n+1*. The value *p* of the amount of lost precision is the number of advice bits we need -- once we have those last few bits from an oracle, we will know the number of programs of length *n+1* that halt. We can then run all such programs in parallel until that many halt, and we can select the longest-running such program as *BB(n+1)*.

Note that, at first glance, this doesn't get any better results than the procedure described in [^1]. The number of halting programs of length *n+1* is potentially *2<sup>n+1</sup>*, requiring a non-prefix-free bit coding of length *n+1*, meaning that every single one of the bits lost when calling *doesThisManyHalt* will contribute to the imprecision *p*. In particular, since the definition of *doesThisManyHalt* requires some constant *C* bits and *len(enc(n))* is of size *O(log(n))*, we again need *O(log(n)) + C* advice bits to determine *BB(n+1)*.

However, the number of halting prefix-free programs of length *2<sup>n+1</sup>* is much less than *2<sup>n+1</sup>*. In fact, the number of such programs decreases fast enough, relative to *2<sup>n+1</sup>*, that we can fit in our prefix-free coding of *n*.

### Upper bounds on the number of halting programs

The definition of Chaitin's constant: over all programs *p*, *Ω = sum(2<sup>-｜p｜</sup>) ｜ p halts*. However, instead of this formulation, consider the function *f(n)* which is the fraction of programs of length *n* that halt, i.e. for each *n* there are *2<sup>n</sup>f(n)* programs of length *n* that halt. Because each halting program of length *n* contributes *2<sup>-n</sup>* to Chaitin's constant, we have *Ω = sum(2<sup>n</sup>f(n)2<sup>-n</sup>) = sum(f(n))* for all *n = 1 → ∞*. This means that *f(n) < n<sup>-1</sup>* for (asymptotically) all *n*, since the harmonic series diverges and Chaitin's constant does not. The same goes for *f(n) = (n log(n))<sup>-1</sup>* and *f(n) = (n log(n) log(log(n)))<sup>-1</sup>* and so on, until we get *f(n) <= iterLogProduct(x)<sup>-1</sup>*. 

> Aside: this doesn't necessarily apply for __all__ *n*, just the vast majority, with probability approaching 1 as *n* tends to infinity. We can easily construct an example where this doesn't hold for a single *n*. Consider the prefix-free language which is defined: 
> - if the first bit is a zero, treat the rest of the stream as input to the interpreter of some other prefix-free language (Lisp etc)
> - if the first bit is a one, read exactly *2⇈20* bits, halting if the last bit is even
> 
> Suppose we knew *BB(2⇈20)*. In this case, the candidate for *doesThisManyHalt* for *BB(n+1)* is *O(n)* bits long (specifically, *2⇈20 - 1* bits). So, we'd still need *O(log(n))* bits of precision from *doesThisManyHalt* to determine *BB(n+1)* for this particular value of *n*.

So, for almost all cases (and probably actually all of them for sensible languages), *f(n) < iterLogProduct(n)<sup>-1</sup>*. So the maximum bits required for the candidate of *doesThisManyHalt* is:

```
requiredBits = log(2^n * f(n))
             < log(2^n * iterLogProduct(n)^-1)
             < n - log(iterLogProduct(n))
             < n - iterLogSum(n)
```

Returning to *doesThisManyHalt*, the number of bits of the candidate is equal to *n - C - len(enc(n)) - len(enc(p))*. Then, the number of advice bits is the required number of bits minus the number of bits in the candidate, or:

```
adviceBits = requiredBits - candidateBits
           < n - iterLogSum(n) - candidateBits
           < n - iterLogSum(n) - (n - C - len(enc(n)) - len(enc(p)))
           < n - iterLogSum(n) - (n - C - iterLogSum(n) - iterLogSum(p))
           < C + iterLogSum(p)
```

However, *p* is equal to the number of advice bits, whose upper bound as shown above is independent of *n*. So, with probability approaching 1 as *n* approaches infinity, the number of required advice bits is a constant. ∎

---

I'm not completely confident in this proof, particularly the hand-waviness around *iterLogSum(x)* vs *log(iterLogProduct(x))* vs *len(enc(x))*. Also, I'm sure there's a much clearer way to express the idea of the asymptotically-increasing probability that the conditions hold, but I'm not familiar enough with the literature to know the standard way to phrase that. That said, it does __feel__ true -- in sequence A195691 [^5], you can see that while the number of lambda terms of a given length does increase, it still holds that *log(A195691(n)) < n - iterLogSum(n)*. For example, *log(A195691(44)) = log(104234931) <= 27*, while *44 - iterLogSum(44) = 44 - 13 = 31*. 

It would also be worth investigating the occasional breaking cases. While it could theoretically occur infinitely many times (just infinitely less often), I suspect that for any sensible language it never actually happens. Whether this is true, and what exactly "sensibe" means, aren't obvious. 

---

[^1]: Scott Aaronson. 2020. The Busy Beaver Frontier. <https://www.scottaaronson.com/papers/bb.pdf>
[^2]: G. Chaitin. To a mathematical theory of evolution and biological creativity. Technical Report 391, Centre for Discrete Mathematics and Theoretical Computer Science, 2010. <https://www.cs.auckland.ac.nz/research/groups/CDMTCS/researchreports/391greg.pdf>.
[^3]: Radó, Tibor (May 1962). "On non-computable functions". Bell System Technical Journal. 41 (3): 877–884. <https://en.wikipedia.org/wiki/Busy_beaver>
[^4]: <https://en.wikipedia.org/wiki/Levenshtein_coding>
[^5]: <https://oeis.org/A195691>

