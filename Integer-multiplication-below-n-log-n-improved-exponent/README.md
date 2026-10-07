# Integer multiplication below n log n: the exponent κ = 2⁻⁷⁴

**Date:** October 7, 2026

An addendum to OpenAI, [*Integer multiplication below n log n*](https://github.com/openai/math/blob/main/preprints/Integer-multiplication-below-n-log-n-September-23-2026/paper.pdf)
(OAI:Integer-multiplication-below-n-log-n-September-23-2026). That preprint gives a
deterministic multitape Turing machine that multiplies two *n*-bit integers in time
O(n (lg n)^(1−κ)) with κ = 2⁻¹⁸², with constants chosen conservatively.

The note shows that the same algorithm, with two local changes and new constants, achieves
**κ = 2⁻⁷⁴**:

- **Axis moves.** The axes of the Gaussian-resampling and Chinese-remainder layouts are moved
  with O(d) direct chunk interchanges instead of O(d²) adjacent ones. This removes the
  condition ε(2−τ) < 1−τ, which forced the dimension exponent ε below 2⁻⁵⁰.
- **Smaller network.** The preprint's address-interchange network is used with ground set of
  size 46 instead of 100. It admits the swap exponent τ = 1 − (6/5)·2⁻³⁶, where the preprint
  uses 1 − 2⁻⁵⁰.
- **Guard width and Gaussian width.** An additive unrolling of the guard-width recursion
  (exponent C₁ = 5) and a smaller Gaussian width allow ε = 3/16.

The first two changes alone give κ = 2⁻⁷⁶. With the preprint's kind of interchange network,
no admissible choice of constants in this architecture gets below about κ = 2⁻⁷³·⁷.

## Files

| File | Contents |
|---|---|
| [`Integer-multiplication-below-n-log-n-improved-exponent.pdf`](Integer-multiplication-below-n-log-n-improved-exponent.pdf) | the note (11 pages) |
| [`Integer-multiplication-below-n-log-n-improved-exponent.tex`](Integer-multiplication-below-n-log-n-improved-exponent.tex) | its LaTeX source (self-contained; `pdflatex`, run three times) |
| [`IntMulKappa.lean`](IntMulKappa.lean) | Lean 4 check of the arithmetic (core Lean, no Mathlib) |
| [`lean-toolchain`](lean-toolchain) | pins Lean 4.34.1, the version used by openai/math |
| [`verify_kappa.py`](verify_kappa.py) | exact-arithmetic check of all constants (Python 3, standard library only) |

## Checking

```sh
python3 verify_kappa.py      # prints the margins and "all checks passed"
lean IntMulKappa.lean        # Lean 4.34.1 (elan reads lean-toolchain); compiles in a few seconds
```

`IntMulKappa.lean` uses no `sorry` and no `native_decide`, and `#print axioms` reports at most
`propext`, `Classical.choice` and `Quot.sound`.

## Scope

The Lean file certifies the exact arithmetic of the improvement:

- the network counts for ground-set size 46;
- the swap-exponent certificates, for example s_b^(5·2³⁶)·m⁶ < (W_b·m)^(5·2³⁶);
- the depth-unrolling lemma and the chain total-variation bound;
- every parameter condition and margin for κ = 2⁻⁷⁴, for κ = 2⁻⁷⁶, and for the preprint's
  original constants (κ = 2⁻¹⁸²).

It does not formalize the machine model, the algorithm, or the structural lemmas. Those are
paper proofs that rely on the rest of the OAI preprint, which is not re-verified here. The
scan over network sizes and the barrier constant 2⁻⁷³·⁷ are checked numerically by
`verify_kappa.py`.

At the time of writing, the openai/math repository (commit `adc7f12`) contains no Lean
formalization of the OAI preprint (family 109).

## Citation

```bibtex
@misc{Integer-multiplication-below-n-log-n-improved-exponent-October-7-2026,
  title  = {{Integer multiplication below $n\log n$: the exponent $\kappa=2^{-74}$}},
  note   = {Addendum to OAI:Integer-multiplication-below-n-log-n-September-23-2026},
  year   = {2026}
}

@misc{OAI:Integer-multiplication-below-n-log-n-September-23-2026,
  author = {{OpenAI}},
  title = {{Integer multiplication below $n\log n$}},
  howpublished = {OpenAI Math Release preprint
                  \href{https://github.com/openai/math/blob/main/preprints/Integer-multiplication-below-n-log-n-September-23-2026/paper.pdf}{OAI:Integer-multiplication-below-n-log-n-September-23-2026}},
  year = {2026}
}
```
