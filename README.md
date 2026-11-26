# dihedral-difference-bases
A research note on difference bases in dihedral groups

[Read the paper (PDF)](paper.pdf) · [LaTeX source](paper.tex) · [Certificate](certificate.json) · [Verifier](verify.py)

## 论文结论

正十一边形的对称群有 22 个元素。从中最少选出 8 个对称操作，就能把每个操作写成两个所选操作的商。把所需数量除以群阶的平方根后，本文证明所有有限二面体群中的最大值为 **8/√22**，在这个群上取到。

这回答了 Banakh 和 Gavrylkiv 在 2019 年论文中提出的第 10 问。他们已经给出十一边形的精确值，并证明了大参数情形。这篇预印本补上有限范围的上界。论文采用 AI 辅助推导和搜索，尚未经外部同行评审。[原文，第 48–49 页](https://gavrylkiv.cnu.edu.ua/wp-content/uploads/sites/188/2024/02/ijgt2019-1.pdf#page=6) · [期刊版](https://doi.org/10.22108/ijgt.2017.21612)

## Reproduce the proof

Run from a checkout with Python 3.8 or later. The checker uses the standard library and makes no network requests.

```sh
python verify.py
```

It checks 69 interval certificates, the explicit difference sets used to sharpen the intervals, and modular witnesses for all gaps. The finite check covers every integer from 1 through 1,212,463. A separate enumeration checks all 54,450 candidate pairs of sizes three and four at n = 11. The infinite tail uses Proposition 11 of the original paper. The proof of the lifting lemma and the precise use of Singer's theorem are in the PDF.

## Research record

The project began with the authors' precise question and cutoff. The search varied two small integer sets, keeping track of which differences supplied rotations and which supplied reflections. The resulting templates covered intervals of parameters. Direct search supplied witnesses for the remaining small cases. Only explicit sets and exact integer checks enter the finite certificate. The literature search located the original question and related cyclic constructions. Priority has not been independently established.

For workflow, we consulted the [Erdős problem database](https://github.com/teorth/erdosproblems) for the distinction between problem statements and status records, and [MathCheckRamsey](https://github.com/ConDug/MathCheckRamsey) for the practice of shipping a checkable computational result. The mathematical inputs are credited in the paper.

To rebuild the PDF, run `pdflatex paper.tex` twice in the repository directory.
