# Writing these notes

Use technical titles that identify the mathematical object, implementation, or test result. Avoid slogans and rhetorical questions in headings.

## Editorial conventions

- **Use descriptive headings.** Name the mathematical object, result, or implementation boundary. For example, use “Two-adic tensor contraction” instead of an imperative tagline.
- **Start with the object.** A definition, equation, counterexample, trace or exact parameter is better than a paragraph saying why the topic matters.
- **Say what happened.** “At \(s=10^6\), \(u_0=0\)” is useful. “Pre-asymptotic parameter ineligibility remains a critical challenge” is not.
- **Keep the boundary close to the claim.** “This checks the original frontend, not the counter” is enough. Do not open every section with a disclaimer.
- **Do not sell experiments.** “Rank fell from 64 to 8” is an observation; “the algorithm is optimized” needs a total-work measurement.
- **Use named source objects.** `QueryStreamProgram.command`, `FnBody.sproj`, `p_t`, the Git SHA, the first divergent state. Avoid “the component”, “the capability” or “the solution” when a precise name exists.
- **Explain a failed idea.** Give its smallest counterexample and what the failure rules out. Do not bury it in an “opportunities” table.
- **Use tables for comparison**, not as a substitute for reasoning. Wide four-column status grids are hard to read, especially on a tablet.
- **Keep history dated.** Old PR conclusions are evidence about an old head, not a live implementation status.
- **No ornamental words.** Avoid “comprehensive”, “robust”, “seamless”, “leveraging”, “state-of-the-art”, “exciting”, “key takeaway”, “non-negotiable” and “game-changing” unless there is a literal, testable reason to use them.
- **No hidden work.** If a theorem, oracle, paper or CI check was not run, say so. Never pass an unsupported branch as zero, or a brute-force oracle as the original computation.

## Page structure

1. **Question:** one sentence.
2. **Object:** the equation, source declaration or input family.
3. **Result:** theorem, measurement, failure, or open condition, plainly named.
4. **Reason:** the smallest derivation or counterexample that makes the result intelligible.
5. **Next test:** what would establish the missing part.

Skip sections that add no information. Some pages need a single proof and nothing else.

## Example

**Before**

> The following section outlines a high-priority optimization opportunity around
> polynomial overhead and associated validation requirements.

**After**

> The field setup searches up to \(2^e\) polynomials with \(e=4\lceil\log_2 s\rceil\).
> That is an avoidable \(s^4\)-size candidate space. Construct a certified
> irreducible polynomial directly, then measure setup time and bit work.

## Evidence labels

Use **proved**, **executed**, **measured**, **refused**, or **proposed** with their ordinary meanings. If the claim depends on a specific source commit, toolchain, code path or hypothesis, put it in the same paragraph.

Avoid multiplying status badges. A working link to the exact source or failed test tells more.
