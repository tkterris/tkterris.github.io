---
modified_date: 2025-03-20
---
# Deriving BB(n+1) from BB(n) with O(log(log(n))) advice bits

## Introduction

In section 5.5, Theorem 20 of The Busy Beaver Frontier[^1], Scott Aaronson describes proof 5.1 by Chaitin[^2] that implies that, for any universal prefix-free language *L*, *K(BB<sub>L</sub>(n+1) \| BB<sub>L</sub>(n)) = O(log n)*, where *K(A\|B)* is the Kolmogorov complexity of *A* given the input string *B*. That is, if you know the *n*'th Busy Beaver, you could determine *BB<sub>L</sub>(n+1)* with *O(log n)* additional bits. At the end of the section, Aaronson poses the following question:

> On the other hand, for bit-based programs, could Theorem 20 be improved to get the number of advice bits below O(log n)—possibly even down to a constant? How interrelated are the successive values of BB(n)?

In this post, I give a proof that the required number of advice bits needed to determine *BB<sub>L</sub>(n+1)* from *BB<sub>L</sub>(n)* is *O(log(log(n)))*, for [almost all](https://mathworld.wolfram.com/AlmostAll.html) *n*. This uses a similar approach to that used in [^1], but instead of incrementally checking lower bounds to Chaitin's constant, we incrementally check a tally of the number of programs of length *n+1* that halt.

The intuitive reason why the proof provides better bounds than Theorem 20[^1] comes from the fact that that Chaitin's constant is "overpowered" for determining whether a program halts. The first *n+1* bits of Chaitin's constant, *Ω<sub>n+1</sub>*, can determine the number of halting programs of length *n+1*, denoted *H<sub>n+1</sub>*, and therefore *BB<sub>L</sub>(n+1)*. However, *Ω<sub>n+1</sub>* also encodes information about much larger programs. *Ω<sub>n+1</sub>* tells you *H<sub>n+2</sub>* within a factor of 2, *H<sub>n+3</sub>* within a factor of 4, and so on. That's a lot to ask from just *BB<sub>L</sub>(n)*, requiring *O(log(n))* advice bits to make up the difference to generate *Ω<sub>n+1</sub>*. However, by focusing solely on *H<sub>n+1</sub>* rather than later values of *H*, we reduce the "level of effort". Usually, anyway -- if *H<sub>n+1</sub>* is very large, then that *does* tell you something about *H<sub>n+2</sub>* and so on (because the language is prefix-free, a large number of halting programs of length *n+1* "rules out" many longer programs), which means you would need those additional advice bits. However, it turns out that the asymptotic density over *n* of such large values of *H<sub>n+1</sub>* is 0.

More precisely: [Lemma (1)](#lemma1) shows that for almost all *n*, *log(H<sub>n+1</sub>)* is less than *n - log(n)*. [Lemma (2)](#lemma2) provides a method for determining *H<sub>n+1</sub>* with a number of advice bits that includes *log(H<sub>n+1</sub>)*, the prefix-free encoding of *n*, and *-n*. [Theorem (3)](#theorem3) then puts these two lemmas together: the *-log(n)* term from Lemma (1) cancels *log(n)* of the prefix-free encoding of *n* in Lemma (2), and the *n* term in Lemma (1) is canceled by the *-n* term in Lemma (2). This gets the bound on advice bits to *O(log(log(n)))* for almost all *n*.

##### A note about the language *L*

The "traditional" Busy Beaver game envisioned by Radó [^3] involves *n*-state, two-symbol Turing machines. In this post we will be considering the equivalent function for *n*-bit programs in a prefix-free, universal, and __self-delimited__ language *L*. Programs in a self-delimited language have access to a *read-bit*[^7] primitive function that consumes a single bit from a stream. "Program length" is the sum of the prefix-free "*L*-expression" plus "read bits", the number of times *read-bit* is called. This has a number of implications, though the two most relevant for this proof are:
- We don't have to enforce any requirements about the features or behavior of *L*, other than that it is prefix-free, universal, and self-delimited. 
  - This is because any other prefix-free and universal (not necessarily self-delimited) language *L2* could be run by *L* with a constant bit overhead (dependent on *L* and *L2*). The overhead comes from the length of an *L* expression acting as an *L2*-interpreter, with the subsequent bitstring being in *L2* and passed into the *L2*-interpreter as read bits.
- We can only determine the length of a program in *L* by running that program. That is, the length of the *L*-expression alone can be determined based on the grammar of *L*, but to get the program length -- *L*-expression plus read bits -- we need to see how many times it calls *read-bit*. 
  - In particular: a program *p* with total length *m* will produce the same exact result in *L* if we take the *m+1* bitstring consisting of *p* with a single random bit appended. So, if we want to count how many programs of a certain size halt, we can't just run all bitstrings of that length in *L* and count them, otherwise we'll double-count shorter programs with irrelevant bits appended.

While this does differ from Theorem 20[^1] (which covers "standard prefix-free universal" languages), I'm adding the self-delimited constraint for a few reasons: (1) it matches Chaitin's proof 5.1[^2] and the definition of [Chaitin's constant](https://mathworld.wolfram.com/ChaitinsConstant.html); (2) as mentioned above, it lets us add arbitrary properties to *L* with only a constant overhead; and (3) it makes the arithmetic in Lemma 2 much less tedious.

Examples of languages meeting this property are Chaitin's LISP[^7], Binary Lambda Calculus[^8], and Keraia[^9].

---

## Proof

First, some notation: 
- *H<sub>x</sub>* is the number of halting *L*-programs with program length (*L*-expression plus read bits) equal to *x*. 
- *log(x)* is always base 2, rounded down to the nearest integer.
- *enc(x)* returns the (prefix-free) [Levenshtein coding](https://en.wikipedia.org/wiki/Levenshtein_coding) of the integer *x*. Note that for all *x*, *\|enc(x)\| = log(x) + O(log(log(x)))* and *\|enc(x + 1)\| >= \|enc(x)\|*.
- "Almost all *n*" is meant in the sense described [here](https://mathworld.wolfram.com/AlmostAll.html). That is, the number of numbers less than *n* not satisfying the condition, divided by *n*, tends asymptotically to zero.

#### <span id="lemma1">Lemma 1: For almost all *n*, *H<sub>n</sub> < 2<sup>n</sup> / n*</span>

The definition of Chaitin's constant *Ω* is, for all halting programs *p* in *L*, *Ω = Σ 2<sup>-\|p\|</sup>*. An equivalent expression is *Ω = Σ 2<sup>-n</sup>H<sub>n</sub>* for all *n = 1 → ∞*. This means that: 
- *Ω = Σ 2<sup>-n</sup>H<sub>n</sub>* for all *n = 1 → ∞*
- *Ω >= Σ 2<sup>-n</sup>H<sub>n</sub>* for all *n = 1 → ∞* such that *H<sub>n</sub> >= 2<sup>n</sup> / n*
- *Ω >= Σ 2<sup>-n</sup>2<sup>n</sup>/n* for all *n = 1 → ∞* such that *H<sub>n</sub> >= 2<sup>n</sup> / n*
- *Ω >= Σ 1/n* for all *n = 1 → ∞* such that *H<sub>n</sub> >= 2<sup>n</sup> / n*

So, Chaitin's constant is greater than or equal to some subset of the harmonic series, specifically the subset of *n* where *H<sub>n</sub> >= 2<sup>n</sup> / n*. However, Chaitin's constant is finite, which per Theorem 1 of Lubeck and Ponomarenko[^4] means that the elements of the harmonic series that add to *Ω* must have asymptotic density of 0, so such *n* must have asymptotic density 0. Conversely, *n* such that *H<sub>n</sub> < 2<sup>n</sup> / n* must have asymptotic density 1. ∎

#### <span id="lemma2">Lemma 2: There is a procedure that can be used to determine *BB(n+1)* from *BB(n)* and a number of advice bits, *p*, such that *p <= log(H<sub>n+1</sub>) + O(1) + \|enc(n)\| + \|enc(p)\| - n*</span>

The procedure we demonstrate will be similar to that described in Theorem 20[^1], except with testing approximations of *H<sub>n+1</sub>* rather than approximations of Chaitin's constant. The other primary difference will be a parameter *p*, which will encode the imprecision in our candidate for *H<sub>n+1</sub>*. We describe an *L*-program *doesThisManyHalt* (pseudocode in this footnote: [^11]). In the procedure below, we run this program multiple times, varying the inputs each time. By using *BB(n)* to evaluate whether the program halts on any particular set of inputs, we will be able to arrive at an estimate for *H<sub>n+1</sub>* with *p* bits of precision.

__Inputs and total program size:__ *doesThisManyHalt* consists of its constant-length program definition with two prefix-free inputs appended. Those inputs are *n* (the length of the known *BB(n)*) and *p* (the amount of imprecision in our candidate estimate for *H<sub>n+1</sub>*). The remainder of the program string, evaluated via *read-bit* (rendered in the pseudocode as "*read_bit*"), is the most significant digits of the candidate. These candidate digits are expressed as a simple binary integer rather than prefix-free, with the length inferred from the other inputs: 
- *read bits = n - O(1) - \|enc(n)\| - \|enc(p)\|*

The binary representation of *candidate* is left-padded with zeroes to ensure this equality holds, so *log(candidate) + 1 <= read bits*.

__Program logic:__ First, the number of candidate bits is inferred by subtracting from *n* the length of the program definition (a hard-coded constant) and the lengths of the prefix-free encodings of the inputs *n* and *p*. It reads in the candidate bits as a binary number, and stores that number as *candidate*. The special case where *candidate = 0* is checked, and immediately halts if so. It then iterates through each of the *2<sup>n+1</sup>* strings of length *n+1*, emulating them as *L*-programs in parallel. Whenever one of the programs halts with total size *n+1* bits (both *L*-expression and read bits), it is added to a tally *halted*. If that tally reaches *candidate* multiplied by *2<sup>p</sup>*, then *doesThisManyHalt* halts. 

Recall that halting self-delimiting programs still halt if they have additional bits appended. This would lead to counting shorter programs multiple times, when we don't want to count them at all. So, the *L*-program emulator in *doesThisManyHalt* must track how often *read_bit* is called, so that only those that halt with a total size of *n+1* bits are added to the tally. Similarly, if a program tries to call *read_bit* enough times that its total length would exceed *n+1* bits, the emulator should treat that as a non-halting program. These features of the *L*-program emulator are part of the program definition of *doesThisManyHalt*, adding *O(1)* to the total length of *doesThisManyHalt* and its inputs.

__Estimating H<sub>n+1</sub>:__ Suppose we know *BB(n)*. Because *doesThisManyHalt* plus its inputs are a length *n* *L*-program, we can evaluate whether it halts. This can be used in a test to estimate *H<sub>n+1</sub>* given *BB(n)*: 
- Start with *candidate = 0* and *p = 0*.
- Run *doesThisManyHalt* with prefix-free *n* and *p*, with *candidate* encoded as a non-prefix-free binary string, left-padded so that the full length is *n*. Use *BB(n)* to determine if it halts.
- If *doesThisManyHalt* halts, *H<sub>n+1</sub> >= candidate \* 2<sup>p</sup>*. Increment *candidate* by one. If that pushes the total length (program and inputs) over *n*, reset *candidate* to zero and increment *p* instead. Return to the previous step.
- If *doesThisManyHalt* does not halt, *H<sub>n+1</sub> < candidate \* 2<sup>p</sup>*.

Because the input *p* is adjustable rather than hard-coded, *candidate\*2<sup>p</sup>* can get to *2<sup>n+1</sup>*, the worst-case upper bound of *H<sub>n+1</sub>*, with only *O(log(n))* bits of *p*. That is, for all *n >= \|doesThisManyHalt\| + \|enc(n)\| + \|enc(n+1)\| + 1*, we will eventually find inputs such that *doesThisManyHalt* does not halt.

Take *candidate* and *p* of the run that did not halt. Any run where *p* is incremented resets *candidate* to zero, so the difference between the non-halting run and the halting run just before it must be due to *candidate* being incremented (if *p* were incremented, *candidate* for the non-halting run would be zero, so the run would have halted, a contradiction). So, the inputs for the last halting run must have been *candidate-1* and *p*. This gives us 
- *(candidate - 1) \* 2<sup>p</sup> <= H<sub>n+1</sub> < candidate \* 2<sup>p</sup>*

giving us *H<sub>n+1</sub>* within *p* bits of precision.

If these *p* bits are provided as advice bits, we will have the exact value of *H<sub>n+1</sub>*. We can then run all programs of length *n+1* in parallel until that many halt with total program length *n+1* bits, and we can select the longest-running such program as *BB(n+1)*.

__Upper bounds on *p*:__ Recall from "Inputs and total program size" that:
- *read bits = n - O(1) - \|enc(n)\| - \|enc(p)\|*

TODO this paragraph is gibberish

With the non-halting *p* and *candidate*, we can infer that *read bits = 1 + log(candidate)* exactly, with no padding. Assume otherwise for the sake of contradiction. We can infer that *p > 0* (otherwise we'd have *H<sub>n+1</sub>* precisely, immediately giving us *BB(n+1)*). A run with *p-1* and either *candidate \* 2* or *candidate \* 2 - 1* would not have halted either. However, both of those options use at most one extra bit than running with the winning *p* and *candidate* (since *\|enc(x)\| > \|enc(x-1)\|* for all *x*, and *candidate \* 2* one bit longer than *candidate*). The extra bit of padding with *p* and *candidate* would have allowed for that higher-precision run with *p-1* and either *candidate \* 2* or *candidate \* 2 - 1*, and they both would have been run before (*p*, *candidate*) because *p* is only increased during the process of estimating *H<sub>n+1</sub>*. So, *n* and *candidate* couldn't have been the first inputs such that *doesThisManyHalt* did not halt, a contradiction.

So:
- *log(candidate) >= n - O(1) - \|enc(n)\| - \|enc(p)\|*

To get the the lost precision with the "winning" value of *p*, we take the number of bits to represent *H<sub>n+1</sub>* in a non-prefix-free manner, and subtract the number of candidate bits we were able to find:
- *p = (bits of H<sub>n+1</sub>) - (candidate bits)*
- *p <= log(H<sub>n+1</sub>) + 1 - (n - O(1) - \|enc(n)\| - \|enc(p)\|)*
- *p <= log(H<sub>n+1</sub>) + O(1) + \|enc(n)\| + \|enc(p)\| - n* ∎

__Remarks:__ It is noticeable that, while this Lemma and Theorem 20[^1] use similar procedures (estimating *H<sub>n+1</sub>* or *Ω<sub>n+1</sub>* through iterated runs, tallying halting machines), this Lemma required significantly more paperwork than Theorem 20. This is because Theorem 20 was proving that the advice bits needed were *O(log n)*, but the savings from Lemma 1 provide *exactly* *log n* advice bits. Rather than encoding both *n* and the candidate bitstring in a prefix-free way, which would have simplified the reasoning, we could only get away with encoding a single one of these. 

#### <span id="theorem3">Theorem 3: Given *BB(n)*, *BB(n+1)* can be determined with *O(log(log(n)))* advice bits for almost all *n*</span>

Substituting the upper bound of *H<sub>n</sub>* from [Lemma 1](#lemma1) into the advice bit upper bound from [Lemma 2](#lemma2), we have that for almost all *n* the number of advice bits *p* satisfies: 
- *p <= log(H<sub>n+1</sub>) + O(1) + \|enc(n)\| + \|enc(p)\| - n*
- *p < log(2^(n+1) / (n+1)) + O(1) + \|enc(n)\| + \|enc(p)\| - n* 
- *p < (n + 1) - log(n+1) + O(1) + log(n) + O(log(log(n))) + \|enc(p)\| - n*
- *p < O(1) + O(log(log(n))) + \|enc(p)\|*
- *p < O(log(log(n)))*  ∎

---

## Discussion

Unfortunately, this proof doesn't provide better bounds for "traditional" *BB(n)*, with *n*-state, two-symbol Turing machines. In [^1], Aaronson gives Theorem 21 for such machines, finding that the conditional complexity of *K(BB(n+1) \| BB(n)) = O(n)*. Note that the number of bits to describe an *n*-state Turing machine is *n log(n) + O(n)*, compared to *n* for an *n*-bit program in a universal prefix-free language. If we want to improve the bounds of Theorem 21 using the proof above, we find that the bits "saved" for an *n*-state Turing machine would be only *O(log(n))*. So, the required bits would still be *O(n)*.

An interesting conclusion is that all but *O(log(log(n)))* programs of length *n+1* halt before *BB(n)*. Specifically, the maximum halting runtime of *doesThisManyHalt* with *n* total bits runs longer than all but *2<sup>O(log(log(n)))</sup>* halting programs of length *n+1*. So, incrementing *n* only adds a relatively small number of "interesting" programs (i.e. programs of length *n+1* that run longer than *BB(n)*). This goes against my intuition that things ought to get "exponentially more interesting" as program lengths increase.

[Lemma 1](#lemma1) lets us save *log(n)* bits due to the harmonic series diverging. But the series *(n log(n))<sup>-1</sup>* diverges as well, as does *(n log(n) log(log(n)))<sup>-1</sup>* and so on. Similarly, the Levenshtein coding of *n* uses *log(n) + log(log(n)) + ... + 2 + log\*(n)* bits (where *log\*(x)* is the [iterated logarithm](https://en.m.wikipedia.org/wiki/Iterated_logarithm) of *x*). So, it seems like we could use the repeated logarithms in the diverging series to save more bits from the encoding of *n*, as we see in [Theorem 3](#theorem3) with the first *log(n)* term. Could the method in [Lemma 2](#lemma2) perhaps do even better than we've shown? As it turns out, probably not.

While it is shown[^4] that a convergent subseries of the harmonic series must have asymptotic density zero, the general case with a convergent subseries of any diverging series of monotonically-decreasing terms doesn't give such strict bounds. Šalát gives Theorem 2[^10] that for such convergent subseries, the density has *lim inf = 0*, and Theorem 1[^10] which includes an example where *lim sup* is nonzero. Nonzero *lim sup* but zero *lim inf* means that, for this to affect the needed advice bits in [Theorem 3](#theorem3) for more than asymptotically zero *n*, the density of *n* where *H<sub>n+1</sub> >= 2<sup>n</sup>(n log(n))<sup>-1</sup>* would have to "jump around" between zero and some nonzero value as *n* tends towards infinity. 

TODO: rephrase this last paragraph

This seems implausible for any sensible language, but because *L* is universal, prefix-free, and self-delimiting, the design space of *L* includes all possible languages (with *O(1)* overhead for an interpreter). Eventually, after that *O(1)* overhead, such pathological examples will contribute to the tally of *H<sub>n+1</sub>*. Similarly, examples that break the "almost all" condition for *O(log(log(n)))* advice bits, such as [^6], will eventually appear with constant overhead.

---

Revised 2025-03-17 with the bound *O(log(log(n)))*. 

---

[^1]: Scott Aaronson. 2020. The Busy Beaver Frontier. <https://www.scottaaronson.com/papers/bb.pdf>
[^2]: G. Chaitin. To a mathematical theory of evolution and biological creativity. Technical Report 391, Centre for Discrete Mathematics and Theoretical Computer Science, 2010. <https://www.cs.auckland.ac.nz/research/groups/CDMTCS/researchreports/391greg.pdf>.
[^3]: Radó, Tibor (May 1962). "On non-computable functions". Bell System Technical Journal. 41 (3): 877–884. <https://en.wikipedia.org/wiki/Busy_beaver>
[^7]: Chaitin, G.J. (1995). [The Limits of Mathematics---Tutorial Version.](https://arxiv.org/pdf/chao-dyn/9509010) arXiv: Chaotic Dynamics.
[^8]: Tromp, John. (2006). [Binary Lambda Calculus and Combinatory Logic.](https://tromp.github.io/cl/LC.pdf) 10.1142/9789812770837_0014. 
[^9]: Michael Stay. 2005. [Very Simple Chaitin Machines for Concrete AIT.](https://arxiv.org/pdf/cs/0508056) Fundam. Inf. 68, 3 (August 2005), 231–247.
[^10]: Tibor Šalát. 1964. [On subseries.](https://resolver.sub.uni-goettingen.de/purl?PPN266833020_0085) Mathematische Zeitschrift, Volume 85, Number 3, 209-225.
[^4]: Lubeck, Brian & Ponomarenko, Vadim. (2018). [Subsums of the Harmonic Series.](https://vadim.sdsu.edu/lp.pdf) The American Mathematical Monthly. 125. 351-355. 10.1080/00029890.2018.1420996. 
[^11]: Pseudocode for *doesThisManyHalt*:
    ```
    doesThisManyHalt(int n, int p) {
        int bitsToRead = n - |doesThisManyHalt| - |enc(n)| - |enc(p)|;
        int candidate = 0;
        int bitsRead = 0;
        while (bitsRead < bitsToRead) {
            candidate = candidate * 2 + read_bit();
            bitsRead++;
        }
        if (candidate == 0) {
            exit;
        }
        int halted = 0;
        getAllProgramsOfLength(n + 1).runInParallel().whenHalt(program -> {
            if (program.expression_length + program.read_bits == n+1) {
                halted++;
                if (halted >= candidate * 2 ^ p) {
                    exit;
                }
            }
        });
    }
    ```

[^6]: Consider the prefix-free language which is defined: 
    - If the first bit is a zero, treat the rest of the stream as input to the interpreter of some other prefix-free language (Lisp etc).
    - If the first bit is a one, continue reading the input until you reach a zero. Set *b* to be the number of initial ones read. Read *2<sup>2<sup>b</sup></sup> - b - 1* bits after the first zero (for a total of *2<sup>2<sup>b</sup></sup>* bits), then halt.
    
    In this case, for all *n* that can be expressed as *2<sup>2<sup>b</sup></sup>* for an integer *b*, the number of bits needed to count *H<sub>n</sub>* is at least:
    - *bits = log(H<sub>n</sub>) + 1*
    - *bits >= log(2^(2<sup>2<sup>b</sup></sup> - b - 1)) + 1*
    - *bits >= 2<sup>2<sup>b</sup></sup> - b - 1 + 1*
    - *bits >= n - log(log(n))*
    
    which means, with the prefix-free encoding of *n* in *doesThisManyHalt*, we'll need *O(log(n))* advice bits for infinitely many *n*. Specifically, for all *n* such that *n=2<sup>2<sup>b</sup></sup> + O(1)*, where the *O(1)* overhead is from the constant length of the interpreter for the above language for *L*. Such *n* occur with density *n<sup>-1</sup>log(log(n))*, which asymptotically approaches zero, so [Lemma (1)](#lemma1) still holds. 

