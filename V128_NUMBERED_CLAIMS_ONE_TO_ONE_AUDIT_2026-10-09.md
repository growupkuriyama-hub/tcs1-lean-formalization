# TCS #1 v128 — 30 numbered mathematical claims × Lean 一対一監査（2026-10-09）

> **判定対象**: `growupkuriyama-hub/Papers/01_fixed-h-cfg/main.tex` の内部版 **v128**、`main` の Git blob `07c53aa9f2bd8c76aa2d29f90f01fbe81e763588`（2026-10-09 確認）。番号付き `theorem` / `proposition` / `lemma` / `corollary` は **30環境**、うち第27項は `\label` がないので原稿中の位置で特定。
>
> **検証した Lean の場所**: `growupkuriyama-hub/tcs1-lean-formalization` の Draft PR #8、`audit/tcs1-v128-exact-delta`。最終的な**コード検証済み checkpoint は CI #890**（2026-10-09、Lean code SHA `e7858324859765065598255ac36cb747aff599e8`）。この文書は **論文の主張と既存宣言の意味論的な対応に関する監査表**であり、独立した30件の Lean theorem statements を全部再度宣言したという意味ではない。
>
> **再利用の基礎**: `V79ManuscriptClaimAudit.lean`（論文順の `#check` 対応表）、`V79TheoremSurfaceAudit.lean`、`V88FullManuscriptAudit.lean`、`MainTheoremMaterializedPackage.lean`、`MaterializedProductionCost.lean`、`V83TypedThicknessWitnessBounds.lean`。旧版の一対一監査は原稿 v79 → v88 の同期で検査済み。ただし **`#check` は宣言の存在・型検査であって、v128 原稿との文言一致を自動証明するものではない**。旧版の補題と v128 の追加条件を混同しない。
>
> **判定語**:
> - **R（再利用）**：対応する旧版または既存 v128 の Lean 数学的定理を特定でき、主張の中核は再証明不要。完全な manuscript-exact な型の等価性の監査とは区別。
> - **B（橋渡し）**：旧版の証明は使えるが、v128 の表示・学習器・定量化・強い複雑性評価との結合に追加検証が必要。
> - **P（部分）**：Lean で一部だけ立証。通常の外部既知定理を使う箇所は明示。
> - **O（未閉鎖）**：当該 v128 主張全体を discharge する Lean 定理が確認できない。論文内の証明が数学的に誤りという判定ではない。

## 原稿順：30件の照合表

| # | v128 原稿ラベル（行） | 既存 Lean の具体的な対応先 | 判定 | 残り・注意点 |
|---:|---|---|:---:|---|
| 1 | `prop:regular-auto` (308) | `regular_auto_proposition_package`; `regular_exists_fixedHSubstitutable` | **R** | 有限モノイドによる正規言語認識・構文合同と正規→fixed-h を旧版で監査。 |
| 2 | `prop:finite-info-closure` (343) | `fixedHSubstitutable_inter_product`; `fixedHSubstitutable_regularFilter_product`; `inverseImage_fixedHSubstitutable_with_erasureFlag` | **P** | (i) 証明済み。(ii) の RS 側、(iii) の消去フラグ付き RS 側は Lean にあるが、両方の **CFL 閉包**（正規言語との共通部分、逆準同型像）は外部の古典定理であり、v128 の `\Ccf{}` の結論へ接続する Lean theorem は未確認。原稿もこの2つを標準的閉包性として引用。 |
| 3 | `prop:yl-special` (459) | `fixedWindowSubstitutable_iff_fixedHSubstitutable` | **R** | 固定 `(k,ℓ)` に対応する `h_{k,ℓ}` のクラス同値。 |
| 4 | `thm:main` (518) | `indexedFixedH_learning_materialized_core`; `corollary_poly_update_materialized`; `indexedClassicalFixedWindowSection7_package`; `indexedLinear_characteristic_package`; v128 新規の `V128SubstringTabulatedGrammar` | **B** | (i)–(iii) は既存の意味論・Gold・多項式 envelope を再利用。ただし **v116 の具体的 `\mathcal B_h`** と旧版の学習器の構築計算量を原稿の表現で統合した最終 lemma は未確認。(iv) は `prop:li-window` と `cor:li-thickness` の未閉鎖部分に依存。(v) 線形部は再利用可能。 |
| 5 | `prop:li-window` (558) | `FixedWindowExactEquivalence.lean`（従来の固定窓 special case）および `SyntacticRefinementRegularity.lean`（一般的 refinement） | **O** | **正の像半群が locally trivial ⇔ 正語上のある固定窓 kernel refinement**、明示 `(n,n)`、固定窓の正の像の局所自明性、`KL=\bigcup RS_h` と CFL 版の全セットは、既存ファイルからの完全な単一定理として確認できない。原稿の証明は Pin 2025 の有限半群事実に依拠。 |
| 6 | `lem:sample-consistency` (653) | `sample_consistency` | **R** | 観測標本の生成。 |
| 7 | `thm:soundness` (664) | `batchLanguage_sound`; `substringBatchLanguage_eq_batchLanguage` | **R** | v116 の言語同値を経由して旧版 soundness をそのまま利用可能。 |
| 8 | `prop:typed-core` (801) | `concreteTypedActive_language_eq_untyped`; `typedDerives_yield_type`; **`retainedTypedNonstartLanguage_eq_inter_fiber`** | **R** | v128 で明記された各 retained non-start `A_μ` の言語と `h`-fiber の等号には既存の専用 v128 ファイルが対応。 |
| 9 | `thm:complete` (863) | `canonicalWitnessWords_completeness`; `substringBatchLanguage_eq_batchLanguage` | **R** | 有限 witness ⇒ 再構成の完全性。v116 へは証明済み言語同値を用いる。 |
| 10 | `thm:reconstruction-fixed-h` (910) | `exact_reconstruction_of_qualitative_reducedness`; `finiteSubstringBatchLanguage_eq_batchLanguage`; **`v116TabulatedBatchLanguage_eq_batchLanguage`** | **R** | 任意の有限標本 K（空標本・epsilon を含む）に対する明示 finite CFG と旧 `BatchLanguage` の同値は CI #858 で証明済み。 |
| 11 | `cor:ilt` (925) | `indexedFixedH_concreteGold_identification_nonempty`; `materializedConservative_gold_identification_explicit`; `v116TabulatedBatchLanguage_eq_batchLanguage` | **B** | Gold 同定の数学は旧版にある。**v116 をそのまま hypothesis とする逐次 `A_h`** が旧実装と同じ言語を各 stage で保持する、という版固有の包装は旧版からの bridge として明示する余地。 |
| 12 | `thm:poly-build` (961) | `MaterializedProductionCost.lean`; `reconstructionRuleCandidateSpace_card_le_fourth`; `substringBucketKeys_unaryCandidateCount_le_cube`; **`v116BinaryRuleTable_card_le_cube`**; **`v116EffectiveBinaryWordTable_eq_actual`**; `substringV116DirectOutputBudget_le_quartic` | **B** | **旧版の多項式 scan/comparison accounting は証明済み**。v128 の **B/U 各三次候補と文字列記述量四次**は別途証明済みだが、v116 の U/L/S/epsilon の**有効出力器全体**や `O(n_K^4)` の候補実行コスト（factor ID・h 型キャッシュ・重複除去）までは閉じていない。原稿の *定理文* は「多項式時間」、*証明本文* が具体的 `O(n_K^4)` を述べる。旧 O(n^5) envelope で新版の四次を証明したことにしてはならない。一方、Lean コンパイラの機械語1ステップずつの意味論は原稿レベルの必須義務ではない。 |
| 13 | `lem:typed-thickness-bound` (1025) | `reachingSpine_context_length_le_card_sub_one`; `canonicalWitnessWords_length_le_typedThickness`; `canonicalWitnessFinset_sampleNorm_le_typedThickness`（`V83TypedThicknessWitnessBounds.lean`） | **R** | typed-yield による reaching context / witness 数・長さ評価。原稿の特定の係数まで型で一致するかは最終 strict 型監査で確認。 |
| 14 | `cor:typed-thickness-data` (1071) | `canonicalWitnessFinset_sampleNorm_le_typedThickness`; `indexedFixedH_exists_characteristic_sample` | **R** | typed thickness の上界＋再構成完全性を合成。 |
| 15 | `prop:typed-thickness-gap` (1088) | **`v128_exponential_gap_manuscript_instance`**; `v128_exponential_gap_explicit_bounds` | **R** | 固定2元型、線形 grammar size、ordinary thickness 1、typed thickness 指数の v128 実例は CI #798 以降の専用証明で確認済み。 |
| 16 | `lem:window-typed-yield` (1166) | `fixedWindow_reduced_minimal_typed_yield_length_le` | **R** | 固定窓による canonical typed yield 長評価。 |
| 17 | `thm:window-thick` (1176) | `concreteFixedWindowSection7_package`; `classicalFixedWindowSection7_package` | **R** | SSBNF での厚みと正例特性標本上界。 |
| 18 | `prop:thick-ssbnf-normal` (1196) | `indexed_proposition74_full_package`; `proposition74_thickness_from_yieldBound` | **R** | source CFG → reduced SSBNF の言語、サイズ、厚みの多項式変換。 |
| 19 | `cor:li-thickness` (1209) | `retainedTypedNonstartLanguage_eq_inter_fiber`; `typedStartBinary_children_derivations_survive_trim`; `fixedWindow_reduced_minimal_typed_yield_length_le`; `indexed_proposition74_full_package` | **O** | 部品は存在するが、**locally trivial な h → fixed-window typing の kernel refinement → retained typed thickness の比較 → characteristic data** という合成の最終 Lean corollary は未確認。#5 の証明を先に閉じれば旧版の固定窓 witness bounds を大部分再利用可能。 |
| 20 | `prop:linear-normal` (1258) | `indexedLinear_normalization_source_package`; `indexedLinear_normalization_language_eq`; `indexedLinear_normalization_shape`; `indexedLinear_normalization_size_le` | **R** | 線形 CFG の spine-based reduced SSBNF 正規化。 |
| 21 | `lem:linear-short` (1273) | `minimumCanonicalYield_linear_length_le`; `minimumCanonicalContext_linear_length_le` | **R** | typed 最短 yield / canonical context の評価。 |
| 22 | `thm:linear-poly` (1281) | `indexedLinear_characteristic_package` | **R** | 任意の固定型で線形言語の特性標本を多項式サイズに限定。 |
| 23 | `prop:linear-separator-example` (1371) | `lpm_proposition86_full_semantic` | **R** | `L_{±,e}` の線形・非正規・固定型可・CE と全固定窓からの分離。 |
| 24 | `prop:nonlinear-rs-example` (1516) | `DeltaStar.nonlinear_rs_example_full`; `DeltaStar.deltaStar_no_indexedLinear_presentation` | **R** | Delta-star の deterministic CFL、nonregular、nonlinear、fixed-h 可、非固定窓を旧版で一体監査。 |
| 25 | `thm:ctr-non-kl` (1592) | `CappedCounter.theorem_ctr_non_kl` | **R** | 全 `ρ≥2` の固定窓分離。 |
| 26 | `lem:finite-monoid-obstruction` (1617) | `finiteMonoid_obstruction`; `finiteMonoid_obstruction_uniform` | **R** | 無限の相互交差・分布相異ファミリーが有限型で分離不可能。 |
| 27 | **ラベルなし** `corollary` (1636) | `UncappedCounter.not_fixedH` | **R** | 原稿の `CTR ∉ RS(Σ_c)`。ラベル欠落は監査用に「原稿1636行」として追跡。 |
| 28 | `cor:dyck-not-rs` (1655) | `DyckOne.not_fixedH` | **R** | Dyck 一種の finite typing に対する障害。 |
| 29 | `lem:rs-fixed-quotient` (1669) | `fixedHSubstitutable_fixedRightQuotient` | **R** | 同じ `h` の固定語右商での substitutability 保存。 |
| 30 | `prop:clark-congruential-comparison` (1700) | `proposition99_fixedH_inclusion`; `proposition99_dyck_properness` | **R** | CONG 包含と二文字アルファベットでの真包含。 |

**30件の整理**：**R=24**、**B=3**（#4,#11,#12）、**P=1**（#2）、**O=2**（#5,#19）。**R=24 とは「24件の v128 完全同期証明が新規に作られた」という意味ではなく、「対応する既存 Lean 定理の再利用先が具体的に特定できた」という意味**である。型の細部や外部閉包事実の扱いは上記に記したとおり。

## 最優先の数学的差分（再証明を避ける）

1. **`prop:li-window`**（#5）：まず使う Pin 2025 の2つの有限半群事実を *明示的な有限半群 lemma または引用する外部境界* として固定し、`ker h_{n,n}|Σ⁺ ⊆ ker h|Σ⁺` の含意と逆含意を Lean でつなぐ。固定窓の `h_{k,ℓ}` 定義と refinement monotonicity は既存のものを使う。
2. **`cor:li-thickness`**（#19）および `thm:main` (iv)：#5 の kernel refinement の上に、v128 専用の retained typed fiber 言語等式と trimming-successful-branch 補題、旧版の fixed-window/normalization/typed-thickness witness bounds を合成。新しい学習器・古い Section 7 を作り直さない。
3. **`prop:finite-info-closure`**（#2）：既存の RS 側3命題は再利用。もし manuscript-exact な **Lean 定理文**が必要なら、CFL と regular language の共通部分および inverse homomorphism 閉包を既存 mathlib / 外部既知定理から引用して `\Ccf{}` 部分まで package する。一般的な古典定理の再証明はしない。
4. **`thm:poly-build`**（#12）と `thm:main` (i),(iii)：旧 v79 の `MaterializedProductionCost` / `MainTheoremMaterializedPackage` は**本当に存在する**。最新の CI #890 では v116 **計算可能な B テーブルが正しい**ことも証明済み。残りの U（バケット）と L/S/ε の実出力、型・context キャッシュ、符号化・候補走査の**抽象的 operation-count** に対する新版 `O(n_K^4)` を評価する。**低レベルの Lean evaluator / CPU semantics を新しい必須基準にしない**。
5. **`cor:ilt`**（#11）：旧版の逐次 learner をそのまま使いつつ、v116 の exact language と旧 BatchLanguage の等式を hypothesis sequence へ持ち上げるだけで足りるか点検。

## 形式化と監査の境界

- `V79ManuscriptClaimAudit.lean` の各 `#check` と `V79FullManuscriptAudit.lean` にある `True` marker は**監査チェックポイント**であり、「全文が Lean の一個の定理として証明された」ことの代替ではない。実際の正しさの根拠は各ファイル内の**非自明な型をもつ定理の proof term**である。
- 旧 v79 `MaterializedProductionCost.lean` は最初から **比較・候補走査回数の組合せ的上界**であると明記し、CPU の machine-code step semantics を主張していない。以前の「検証済み」の解釈にこれを含めてよいが、v128 本文が明記した**四次の特別な上界**への橋渡しは別。
- 新規 `V128FiniteInformationClosure` は (i) と (ii) の RS 側、`V128ErasureFlagTyping` は (iii) の RS 側まで。CFL 閉包は数学的には標準定理として原稿が引用している。Lean 内にないことを「論文の誤り」と混同しない。
- `prop:li-window` の標準文献依存は Pin 2025 で、これに依拠する `cor:li-thickness` が新規の本質的な追加部分。論文としての引用依存と、**Lean の完全内部証明**は別。
- **未監査の対象**：番号のない重要な文中主張、定義の厳密なバージョン一致、v128 の各 theorem statement と Lean の型の数学的な全称量化の最終突合、全 theorem からのトラスト境界（外部定理・axiom・定義への依存）を *一行ずつ* 自動検査する artefact。この表は30件の対応の first-pass 正本であり、未完の `#5/#19` を証明済みに言い換えない。

## ソースと固定した検証点

- [v128 原稿（Papers/main.tex）](https://github.com/growupkuriyama-hub/Papers/blob/main/01_fixed-h-cfg/main.tex)
- [v79 一対一監査 Lean](./LeanCfgProject/TCS1/V79ManuscriptClaimAudit.lean)
- [v79 theorem surface](./LeanCfgProject/TCS1/V79TheoremSurfaceAudit.lean)
- [v88 exact version audit](./LeanCfgProject/TCS1/V88FullManuscriptAudit.lean)
- [旧版の production cost](./LeanCfgProject/TCS1/MaterializedProductionCost.lean)
- [v128 差分監査](./FORMALIZATION_TCS1_V128_DELTA.md)
- [CI #890 code checkpoint](https://github.com/growupkuriyama-hub/tcs1-lean-formalization/actions/runs/37830187537)

**この監査では旧版の Lean 定理・主張を変更していない。** main、提出済み TCS 原稿、v88 tag/release も無変更、PR #8 は Draft。
