---
modified_date: 2025-03-17
---
# Deriving BB(n+1) from BB(n) with O(log(log(n))) advice bits

## Introduction

In section 5.5, Theorem 20 of The Busy Beaver Frontier [^1], Scott Aaronson describes a proof by Chaitin [^2] that, for any universal prefix-free language *L*, *K (BB<sub>L</sub>(n+1) \| BB<sub>L</sub>(n)) = O(log n)*, where *K(A\|B)* is the prefix-free Kolmogorov complexity of *A* given the input string *B*. That is, if you know the *n*'th Busy Beaver, you could determine *BB<sub>L</sub>(n+1)* with *O(log n)* additional bits. At the end of the section, Aaronson poses the following question:

> On the other hand, for bit-based programs, could Theorem 20 be improved to get the number of advice bits below O(log n)—possibly even down to a constant? How interrelated are the successive values of BB(n)?

In this post, I sketch a proof that the required number of advice bits needed to determine *BB<sub>L</sub>(n+1)* from *BB<sub>L</sub>(n)* is *O(log(log(n)))*, for [almost all](https://mathworld.wolfram.com/AlmostAll.html) *n*. This uses a similar approach to that used in [^1], but instead of incrementally checking lower bounds to Chaitin's constant, we incrementally check a tally of the number of programs of length *n+1* that halt.

Note that while the Busy Beaver game envisioned by Radó [^3] involved *n*-state, two-symbol Turing machines, in this post we will be considering the equivalent function for *n*-bit programs in a prefix-free universal language *L* (the choice of language itself doesn't matter; the results are equivalent for Lisp, Zot, Binary Lambda Calculus, or any other such language). So, from here on out, *BB(n)* specifically means *BB<sub>L</sub>(n)*. Also, we're doing computer science today, so every *log* you see is the logarithm base 2, rounded down to the nearest integer.

---

## Proof

First, some notation: 
- *H<sub>x</sub>* is the number of halting L-programs of length exactly *x* bits (program plus input). 
- *enc(x)* returns the (prefix-free) [Elias omega coding](https://en.wikipedia.org/wiki/Elias_omega_coding) of the integer *x*. Note that for all *x*, *\|enc(x)\| = log(x) + \|enc(log(x))\| + O(1) = log(x) + O(log(log(x)))*.
- When I say a condition applies for "almost all *n*", I mean it in the sense described [here](https://mathworld.wolfram.com/AlmostAll.html). That is, as *n* increases, the probability that the condition holds asymptotically converges on 1.

#### <span id="lemma1">Lemma 1: For almost all *n*, *H<sub>n</sub> < 2<sup>n</sup> / n*</span>

The definition of Chaitin's constant *Ω* is, for all programs *p*, *Ω = Σ<sub>p halts</sub> 2<sup>-\|p\|</sup>*. However, we could instead express it as *Ω = Σ<sub>n = 1 → ∞</sub> H<sub>n</sub>2<sup>-n</sup>*. This means that: 
- *Ω >= Σ<sub>n = 1 → ∞ \| H<sub>n</sub> >= 2<sup>n</sup> / n</sub> H<sub>n</sub>2<sup>-n</sup>* 
- *Ω >= Σ<sub>n = 1 → ∞ \| H<sub>n</sub> >= 2<sup>n</sup> / n</sub> 2<sup>n</sup>/n \* 2<sup>-n</sup>*
- *Ω >= Σ<sub>n = 1 → ∞ \| H<sub>n</sub> >= 2<sup>n</sup> / n</sub> 1/n*

So, Chaitin's constant is less than some subset of the harmonic series, specifically the subset of *n* where *H<sub>n</sub> >= 2<sup>n</sup> / n*. However, Chaitin's constant is finite, which per Theorem 1 of Lubeck and Ponomarenko[^4] means that the elements of the harmonic series that add to *Ω* must have asymptotic density of 0, so such *n* must have asymptotic density 0. Conversely, *n* such that *H<sub>n</sub> < 2<sup>n</sup> / n* must have asymptotic density 1. ∎

#### <span id="lemma2">Lemma 2: There is a procedure that can be used to determine *BB(n+1)* from *BB(n)* and a number of advice bits, *p*, such that *p = log(H<sub>n+1</sub>) + O(1) + \|enc(n)\| + \|enc(p)\| - n*</span>

Consider the following pseudocode:

```
doesThisManyHalt(int candidate, int p) {
    int n = |doesThisManyHalt| + |enc(candidate)| + |enc(p)|;
    int halted = 0;
    getAllProgramsOfLength(n + 1).runInParallel().whenHalt(program -> {
        if (program.consumedBits == n+1) {
            halted++;
            if (halted > candidate * 2 ^ p) {
                exit;
            }
        }
    });
}
```

__Inputs and total program size:__ *doesThisManyHalt* takes a prefix-free encoding of a candidate value for *H<sub>n+1</sub>* (with *p* least-significant bits truncated from the candidate) and a prefix-free encoding of the number of truncated bits *p*. Including the program definition itself, the total number of bits consumed is *n*. That is, *n = \|doesThisManyHalt\| + \|enc(candidate)\| + \|enc(p)\|*.[^5] 

__Program logic:__ First, *n* is inferred from the length of the program definition (a hard-coded constant) and the lengths of the prefix-free encodings of the inputs. It then iterates through each of the *2<sup>n+1</sup>* program strings of length *n+1*, emulating them in parallel. Whenever one of the programs halts after consuming exactly *n+1* bits (both the program and its inputs), it is added to a tally *halted*. If that tally exceeds the input candidate multiplied by *2<sup>p</sup>*, then *doesThisManyHalt* halts. 

__Estimating H<sub>n+1</sub>:__ Suppose we know *BB(n)*. Because *doesThisManyHalt* plus its inputs are length *n* and prefix-free, we can evaluate whether it halts. This can be used in a test to estimate *H<sub>n+1</sub>* given *BB(n)*: 
- Start with *candidate = 0* and *p = 0*.
- Run *doesThisManyHalt* with inputs *candidate* and *p*. Use *BB(n)* to determine if it halts.
- If *doesThisManyHalt* halts, *H<sub>n+1</sub> >= candidate \* 2<sup>p</sup>*. Increment *candidate* by one. If that pushes the total length (program and inputs) over *n*, reset *candidate* to zero and increment *p* instead. Return to the previous step.
- If *doesThisManyHalt* does not halt, *H<sub>n+1</sub> < candidate \* 2<sup>p</sup>*.

Take *candidate* and *p* of the run that did not halt. Any run where *p* is incremented resets *candidate* to zero, so the run before the non-halting run must have incremented *candidate* rather than *p*. So, the inputs for the last halting run must have been *candidate-1* and *p*. This gives us *(candidate - 1) \* 2<sup>p</sup> <= H<sub>n+1</sub> < candidate \* 2<sup>p</sup>*, giving us *H<sub>n+1</sub>* within *p* bits of precision.

If these *p* bits are provided as advice bits, we will have the exact value of *H<sub>n+1</sub>*. We can then run all programs of length *n+1* in parallel until that many halt after consuming exactly *n+1* bits, and we can select the longest-running such program as *BB(n+1)*.

__Upper bounds on *p*:__ First, we get a bound on the (non-prefix-free) number of candidate bits, *log(candidate)*, for any run of *doesThisManyHalt* in terms of *n* and *p*. We start with *n = \|doesThisManyHalt\| + \|enc(candidate)\| + \|enc(p)\|* from "Inputs and total program size". Then:
- *n = \|doesThisManyHalt\| + \|enc(candidate)\| + \|enc(p)\|*
- *n = O(1) + log(candidate) + \|enc(log(candidate))\| + \|enc(p)\|*
- *log(candidate) = n - O(1) - \|enc(log(candidate))\| - \|enc(p)\|*
- *log(candidate) >= n - O(1) - \|enc(n)\| - \|enc(p)\|*

The last reduction is valid because *candidate <= 2<sup>n</sup>*, so *log(candidate) <= n*.

To get the the lost precision with the "winning" value of *p*, we take the number of bits to represent *H<sub>n+1</sub>* in a non-prefix-free manner, and subtract the number of candidate bits we were able to find:
- *p = (bits of H<sub>n+1</sub>) - (candidate bits)*
- *p <= log(H<sub>n+1</sub>) + 1 - (n - O(1) - \|enc(n)\| - \|enc(p)\|)*
- *p <= log(H<sub>n+1</sub>) + O(1) + \|enc(n)\| + \|enc(p)\| - n* ∎

#### <span id="theorem3">Theorem 3: Given *BB(n)*, *BB(n+1)* can be determined with *O(log(log(n)))* advice bits for almost all *n*</span>

Substituting the upper bound of *H<sub>n</sub>* from [Lemma 1](#lemma1) into the advice bit upper bound from [Lemma 2](#lemma2), we have that for almost all *n* the number of advice bits *p* satisfies: 
- *p <= log(H<sub>n+1</sub>) + O(1) + \|enc(n)\| + \|enc(p)\| - n*
- *p < log(2^(n+1) / (n+1)) + O(1) + \|enc(n)\| + \|enc(p)\| - n* 
- *p < (n + 1) - log(n+1) + O(1) + log(n) + O(log(log(n))) + \|enc(p)\| - n*
- *p < O(1) + O(log(log(n))) + \|enc(p)\|*
- *p < O(log(log(n)))*  ∎

---

## Discussion

Unfortunately, this proof doesn't provide better bounds for "traditional" *n*-state, two-symbol Turing machines. In [^1], Aaronson gives Theorem 21 for such machines, finding that the conditional complexity of *K(BB(n+1) \| BB(n)) = O(n)*. Note that the number of bits to describe an *n*-state Turing machine is *n log(n) + O(n)*, compared to *n* for an *n*-bit program in a universal prefix-free language. If we want to improve the bounds of Theorem 21 using the proof above, we find that the bits "saved" for an *n*-state Turing machine would be only *O(log(n))*. So, the required bits would still be *O(n)*.

An interesting conclusion is that all but *O(log(log(n)))* programs of length *n+1* halt before *BB(n)*. Specifically, the maximum halting runtime of *doesThisManyHalt* with *n* total bits runs longer than all but *2<sup>O(log(log(n)))</sup>* halting programs of length *n+1*. So, incrementing *n* only adds a relatively small number of "interesting" programs (i.e. programs of length *n+1* that run longer than *BB(n)*). This goes against my intuition that things ought to get "exponentially more interesting" as program lengths increase.

It would be worth investigating the cases where the inequality in [lemma (1)](#lemma1) doesn't hold -- while we can construct a language where "only" almost all *n* satisfy it,[^6] I suspect that for any sensible language the result does indeed hold for all *n*. Whether this is true, and what exactly "sensible" means, aren't obvious. Perhaps something involving languages that have minimally-sized interpreters? 

This bound could also potentially be improved, since the unconditional Kolmogorov complexity of *BB(n)* is *n*. The sum of *(x log(x))<sup>-1</sup>* diverges, as does *(x log(x) log(log(x)))<sup>-1</sup>* and so on, so there might be a proof of this tighter bound on *H<sub>n</sub>*. This could be enough to completely equal *\|enc(n)\|*, getting the number of advice bits to a constant. To do that in this proof, though, we'd have to show that a convergent subset of *any* decreasing divergent series has asymptotic density 0, which seems to only have been proven[^4] for the harmonic series.

---

Revised 2025-03-17 with the bound *O(log(log(n)))*. 

---

[^1]: Scott Aaronson. 2020. The Busy Beaver Frontier. <https://www.scottaaronson.com/papers/bb.pdf>
[^2]: G. Chaitin. To a mathematical theory of evolution and biological creativity. Technical Report 391, Centre for Discrete Mathematics and Theoretical Computer Science, 2010. <https://www.cs.auckland.ac.nz/research/groups/CDMTCS/researchreports/391greg.pdf>.
[^3]: Radó, Tibor (May 1962). "On non-computable functions". Bell System Technical Journal. 41 (3): 877–884. <https://en.wikipedia.org/wiki/Busy_beaver>
[^4]: Lubeck, Brian & Ponomarenko, Vadim. (2018). [Subsums of the Harmonic Series](https://vadim.sdsu.edu/lp.pdf). The American Mathematical Monthly. 125. 351-355. 10.1080/00029890.2018.1420996. 
[^5]: If the candidate is too small, it is left-padded with zeroes to ensure this equality holds.
[^6]: Consider the prefix-free language which is defined: 
    - If the first bit is a zero, treat the rest of the stream as input to the interpreter of some other prefix-free language (Lisp etc).
    - If the first bit is a one, continue reading the input until you reach a zero. Set *b* to be the number of initial ones read. Read *2<sup>2<sup>b</sup></sup> - b - 1* bits after the first zero (for a total of *2<sup>2<sup>b</sup></sup>* bits), then halt.
    
    In this case, for all *n* that can be expressed as *2<sup>2<sup>b</sup></sup>* for an integer *b*, the number of bits needed to count *H<sub>n</sub>* is at least:
    - *bits = log(H<sub>n</sub>) + 1*
    - *bits >= log(2^(2<sup>2<sup>b</sup></sup> - b - 1)) + 1*
    - *bits >= 2<sup>2<sup>b</sup></sup> - b - 1 + 1*
    - *bits >= n - log(log(n))*
    
    which means, with the prefix-free encoding of *n* in *doesThisManyHalt*, we'll need *O(log(n))* advice bits for infinitely many *n* (specifically, for all *n* such that *n=2<sup>2<sup>b</sup></sup>*). Such *n* occur with probability *n<sup>-1</sup>log(log(n))*, which asymptotically approaches zero, so [lemma (1)](#lemma1) still holds. It seems unlikely that a "sensible" (whatever that means) language would have such irregular spikes in *H<sub>n</sub>*, but the fact that it can theoretically happen infinitely many times means that this proof only applies for "almost all" *n*.

