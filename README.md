# A 2-adic rigidity theorem for complementary divisors of Mersenne numbers

Yuto Niwa · November 2026

ChatGPT generated nearly all of the manuscript, including the written proof, and generated the Lean formalization. The Lean kernel checked the formal theorem. The human author takes responsibility for the manuscript and its references.

## Theorem

Let $p$ be an odd prime and write $2^p-1=DE$ with natural numbers $D,E>1$. If for some natural number $t>p/4$ both $D-1$ and $E+1$ are divisible by $2^t$, then $(p,D,E)=(11,89,23)$.

The exceptional pair occurs at $t=3$. Indeed, $89\cdot23=2047=2^{11}-1$, and $8$ divides both $88$ and $24$.

- [Manuscript (PDF)](paper/Mersenne-Rigidity.pdf)
- [Manuscript (LaTeX)](paper/main.tex)
- [Formal proof (Lean 4)](MersenneRigidity.lean)
- [Japanese overview](README.ja.md)

## Reproduce the kernel check

With Git, Bash, and [elan](https://github.com/leanprover/elan) installed, run from the repository root:

```sh
bash verify.sh
```

The script checks out mathlib v4.25.2 at commit `c98ae54af00eaefe79c51b2b278361ca94e59bfb`, fetches the required cached dependencies, and runs Lean 4.25.2 on the full proof. The first run needs internet access. The expected final line is:

```text
'MersenneRigidity.mersenne_rigidity' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## License and reuse

The Lean formalization, verification script, and repository documentation are available under the [MIT License](LICENSE). The manuscript PDF and LaTeX source in `paper/` are available under [CC BY 4.0](paper/LICENSE), with [attribution details](paper/NOTICE.md). These permissions apply to the extent Yuto Niwa holds applicable rights. Dependencies and third-party materials retain their own licenses.

Both licenses permit commercial reuse. Preserve the required notices when reusing code. For manuscript reuse, credit the author, link to the license, and identify modifications.

## Citation and feedback

Citation metadata is provided in [CITATION.cff](CITATION.cff). For a reproducible reference to the formalization, also record the commit SHA you used.

Please report mathematical errors, reproduction failures, or relevant prior work through [GitHub Issues](https://github.com/k8-glitch/mersenne-rigidity/issues), with the theorem or file location and supporting details. Proposed corrections can be submitted as pull requests. Contributions should use the license applicable to the edited files, and substantial AI assistance should be disclosed.

## Automated verification

[Verify Lean proof](https://github.com/k8-glitch/mersenne-rigidity/actions/workflows/verify.yml) runs on changes to the proof, verification script, or workflow, and on pull requests affecting those files. Each run checks the proof with the pinned mathlib revision and checks the reported axioms of the main theorem against `propext`, `Classical.choice`, and `Quot.sound`. The run page provides the execution log and result.

The manuscript carries its original August 26, 2026 date. The repository publication date is November 22, 2026.
