# A 2-adic rigidity theorem for complementary divisors of Mersenne numbers

Yuto Niwa · November 2026

ChatGPT generated nearly all of the manuscript, including the written proof, and generated the Lean formalization. The Lean kernel checked the formal theorem. The human author takes responsibility for the manuscript and its references.

## Theorem

Let $p$ be an odd prime and write $2^p-1=DE$ with natural numbers $D,E>1$. If for some natural number $t>p/4$ both $D-1$ and $E+1$ are divisible by $2^t$, then $(p,D,E)=(11,89,23)$.

The exceptional pair occurs at $t=3$. Indeed, $89\cdot23=2047=2^{11}-1$, and $8$ divides both $88$ and $24$.

- [Manuscript (PDF)](paper/Mersenne-Rigidity.pdf)
- [Manuscript (LaTeX)](paper/main.tex)
- [Formal proof (Lean 4)](MersenneRigidity.lean)
- [Japanese overview](https://mersenne-rigidity-niwa.aheadboar1.chatgpt.site)

## Reproduce the kernel check

With Git, Bash, and [elan](https://github.com/leanprover/elan) installed, run from the repository root:

```sh
bash verify.sh
```

The script checks out mathlib v4.25.2 at commit `c98ae54af00eaefe79c51b2b278361ca94e59bfb`, fetches the required cached dependencies, and runs Lean 4.25.2 on the full proof. The first run needs internet access. The expected final line is:

```text
'MersenneRigidity.mersenne_rigidity' depends on axioms: [propext, Classical.choice, Quot.sound]
```
