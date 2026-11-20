# yamagishi-math

Machine-checked statements from the papers of Yuuki Yamagishi (山岸勇輝), written in Lean 4 with Mathlib.

山岸勇輝の論文の定理と法則のうち、数学の中身を Lean 4（Mathlib）で書き、機械に証明を確かめさせたものです。日本語の説明は下にあります。

- Author: Yuuki Yamagishi (ORCID [0009-0006-8587-3450](https://orcid.org/0009-0006-8587-3450))
- Papers: <https://www.yamagishiyuuki.com/yoi/>
- Lean `v4.37.0-rc1`, Mathlib `v4.37.0-rc1` (see `lean-toolchain` and `lake-manifest.json`)
- No `sorry`, no extra axioms, no `native_decide`. The main theorems depend only on the three standard axioms (`propext`, `Classical.choice`, `Quot.sound`).
- The Lean code was written with the assistance of AI (Claude by Anthropic). The statements come from the author's papers, and the author is responsible for the content.

## What is checked

| Paper | File | Main theorems | Statement checked by Lean |
|---|---|---|---|
| [01](https://www.yamagishiyuuki.com/yoi/1) The Uniqueness Theorem of n = 2 for Spherically Symmetric Density Distributions | `Yamagishi/Paper01.lean` | `uniqueness_n2` | For every real n, the shell rate 4π r^(2−n) is constant on r > 0 if and only if n = 2. |
| [02](https://www.yamagishiyuuki.com/yoi/2) The 4π Mass Cancellation Theorem | `Yamagishi/Paper02.lean` | `mass_cancellation_4pi`, `mass_general`, `mass_eq_4pi_iff` | The mass of the unit ball in ℝ³ with density r^(−2) is 4π. For n < 3 the mass is 4π/(3−n), and it equals 4π only for n = 2. |
| [40](https://www.yamagishiyuuki.com/yoi/40) The Four Planck Quantities Are Four Instances of One Rule | `Yamagishi/Paper40.lean` | `two_identities`, `four_quantities`, `eps_eq_mu` | l_P/t_P = c and E_P t_P = ħ for any ħ and G; under G = a, ħ = 1/a the four Planck quantities are c^N or c^N/a, and the power of a equals the mass dimension. |
| [44](https://www.yamagishiyuuki.com/yoi/44) The Power of 4π Is the Mass Dimension | `Yamagishi/Paper44.lean` | `nine_quantities`, `eps_eq_mu` | For nine Planck quantities, the power of a = 4π equals the mass dimension (with k_B = 1 for the temperature). |
| [116](https://www.yamagishiyuuki.com/yoi/116) What Does the Exponent of c Count? | `Yamagishi/Paper116.lean` | `exponent_formula`, `exponent_exists_unique` | For d ≠ 1 the exponent formula holds and the solution is unique (determinant 1 − d). |
| [1128](https://www.yamagishiyuuki.com/yoi/1128) Multiplying by a Speed Once … | `Yamagishi/Paper1128.lean` | `ladder_step`, `adjacent_ratio` | m_P c^k = √(ħ/G) c^(k+1/2); the ratio of neighbouring types is exactly c. |
| [1130](https://www.yamagishiyuuki.com/yoi/1130) Under the Yamagishi Patch, the Power of 4π Plus the Mass Dimension Is Unchanged by Multiplying In G, ħ and c … | `Yamagishi/Paper1130.lean` | `ledger_identity`, `invariant_under_G_hbar_c`, `parity` | With the placement G = a, ħ = 1/a, placed mass m = a: ε + μ = 2r + u + ρ; the sum is unchanged by any powers of G, ħ and c; the parity rule. |
| [1131](https://www.yamagishiyuuki.com/yoi/1131) The Coefficient "1/6" Comes from Two Roots … | `Yamagishi/Paper1131.lean` | `pred_factorial_eq_two_iff`, `factorial_eq_two_mul_iff` | (n − 1)! = 2 if and only if n = 3; for n ≥ 1, n! = 2n if and only if n = 3. |
| [1132](https://www.yamagishiyuuki.com/yoi/1132) The Yamagishi Patch Is Planck Units with Only the Unit of Mass Rescaled by 4π | `Yamagishi/Paper1132.lean` | `patch_is_mass_unit_times_4pi`, `general_rescale` | Among positive rescalings of the units, the patch is the unique one with mass × 4π and length and time unchanged. |

The correspondence between each statement in the papers and each Lean theorem is listed in [`00_対応表.md`](00_対応表.md) (in Japanese).

## What is not checked

- Lean checks the statements as written in Lean. Whether a Lean statement says the same thing as the sentence in a paper is for a human reader to compare; the correspondence table is there for that.
- Only the mathematical content is formalized (exponent bookkeeping, integrals, "if and only if" statements). The physical readings in the papers, such as "this 4π is a solid angle" or "this 4π is a convention", are outside the formalization.
- A machine-checked proof says nothing about novelty. Several of these statements are elementary, and some are known in other forms (for example, the density r^(−2) of Paper 01 is the singular isothermal sphere of astrophysics). The papers themselves say where a statement is elementary or already known.

## How to check it yourself

Install Lean with [elan](https://lean-lang.org/install/), then:

```
lake exe cache get
lake build
```

`lake build` finishes without errors when every theorem in the repository has been checked.

## 日本語の説明

- ここにあるのは、論文の中の数学の言明（指数の勘定、積分、「〜のときだけ」）を Lean 4 で書き、計算機に証明を一行ずつ確かめさせたものです。
- 証明の飛ばし（`sorry`）、自分で足した公理、`native_decide` は使っていません。
- 機械が確かめるのは、Lean で書いた文です。原稿の文と同じことを言っているかは、[`00_対応表.md`](00_対応表.md) で一つずつ読み比べられるようにしてあります。
- 物理としての読み（「この 4π は立体角」「この 4π は約束」など）は、形式化の外にあります。新しい言明かどうかも、機械の確かめとは別の話です。初等的なものや、別の形で知られているもの（論文01 の密度 1/r² は、天文学の特異等温球の形）も含まれます。
- 確かめ直すには、Lean を入れて、上の二つのコマンドを打ちます。
- Lean のコードは、AI（Anthropic の Claude）の助けを借りて書きました。言明は著者の論文のもので、内容の責任は著者にあります。

## License

The Lean code in this repository is released under the Apache License 2.0 (see [`LICENSE`](LICENSE)). The papers themselves are published under CC BY 4.0 at the links above.

Copyright 2026 Yuuki Yamagishi.
