# メルセンヌ数の相補因子の2進剛性定理

*A 2-adic rigidity theorem for complementary divisors of Mersenne numbers*

Yuto Niwa（丹羽悠斗） · 2026年11月22日公開

## 定理

奇素数 $p$ について、$D$, $E$ を1より大きい自然数とし、$2^p-1=DE$ とします。ある自然数 $t>p/4$ で、$2^t$ が $D-1$ と $E+1$ の両方を割り切るなら、次の一組に限られます。

$$
(p,D,E)=(11,89,23)
$$

実際、$2^{11}-1=2047=89\times23$ です。$t=3$ とすると、$89-1=88$ と $23+1=24$ はともに8の倍数で、$3>11/4$ も成立します。

<details>
<summary>Read the theorem in English</summary>

Let $p$ be an odd prime and let $D,E>1$ be complementary divisors of $2^p-1$. If, for some integer $t>p/4$, both $D-1$ and $E+1$ are divisible by $2^t$, then $(p,D,E)=(11,89,23)$.

</details>

## 形式証明

共通の2進深度 $\tau$ を $3\tau<p<4\tau$ に絞り、正規化して得られる二つの方程式を無限降下で調べます。残る数列について、2のべきになる項を分類すると例外の一組が決まります。

- [論文（PDF）](paper/Mersenne-Rigidity.pdf)
- [論文（LaTeX）](paper/main.tex)
- [形式証明（Lean 4）](MersenneRigidity.lean)
- [検証スクリプト](verify.sh)

## 検証方法

Lean と mathlib はともに v4.25.2 です。Git、Bash、[elan](https://github.com/leanprover/elan) を用意し、リポジトリを取得して実行してください。

```sh
git clone https://github.com/k8-glitch/mersenne-rigidity.git
cd mersenne-rigidity
bash verify.sh
```

初回の実行にはインターネット接続が必要です。スクリプトは mathlib のリビジョン `c98ae54af00eaefe79c51b2b278361ca94e59bfb` を使用します。

主定理 `MersenneRigidity.mersenne_rigidity` が依存する公理として Lean が表示したのは `propext`、`Classical.choice`、`Quot.sound` の3つです。期待される最後の出力は次のとおりです。

```text
'MersenneRigidity.mersenne_rigidity' depends on axioms: [propext, Classical.choice, Quot.sound]
```

[GitHub Actions の検証結果](https://github.com/k8-glitch/mersenne-rigidity/actions/workflows/verify.yml)も参照できます。

## 作成と利用について

論文本文・文章による証明のほぼ全体と Lean 形式化は ChatGPT が生成しました。形式化された定理は Lean カーネルで検証しています。人間の著者が論文と参考文献に責任を負います。

形式証明、検証スクリプト、リポジトリの文書には [MIT License](LICENSE)、`paper/` 内の論文PDFとLaTeX原稿には [CC BY 4.0](paper/LICENSE) が適用されます。詳細は[英語README](README.md)と[論文の帰属表示](paper/NOTICE.md)を参照してください。
