# Lehmer Random Number Generator
## Sources
https://en.wikipedia.org/wiki/Lehmer_random_number_generator
https://en.wikipedia.org/wiki/Linear_congruential_generator
https://lpuguidecom.files.wordpress.com/2017/05/multie28093stream-lehmer-rngs.pdf
Almost identical: https://huichen-cs.github.io/course/CSCI570/2016Spring/notes/lecture06_rngs.pdf

## Basic principle
Start with a seed r
Compute next value r' = r * a mod m. This is called "next"
m is 2^31-1 and a is 48271 in this implementation.
Due to m and a being coprime the above calculation generates a sequence of every value between 1 and m before repeating.
This is sufficiently random for non-cryptographic use-cases.

## Problems
The next function computes a step along the circular sequence. If multiple different seeds are used they could be adjacent (either directly or with only a small number of steps) on the sequence. If r1 is 10 "next" steps behind r2 the 11. step of r1 returns the same value as the 1. step of r2. This is somewhat problematic when "splitting" seed, i.e. generating a new seed from the current seed to effectively have two seeds used in seperate streams. The current implementation: split r = (next r, r - next r) could theoretically run into this problem. Due to the birthday paradox this is quite likely to happen at some point. Approximation from wikipedia: p(n) = n²/2m or equivalently: n² = m => p(n) = 1/2. After 2^16 = 65k splits we can expect a repetition in 50% of the cases.
- This may be acceptable
- Multiple streams: Distribute 4 seeds along the sequence and use those for each core separately
- Short-lived seeds: seed n r = (next^n r, next r). This seed can then be used for n random values after which it repeats the values from next^n r and becomes invalid


