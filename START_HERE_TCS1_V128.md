> # ⭐ NEW CHAT: read [NEXT_CHAT_HANDOFF_TCS1_2026-10-10.md](./NEXT_CHAT_HANDOFF_TCS1_2026-10-10.md) FIRST
> **2026-10-10 優先訂正：** このファイルの後続にある「最新 CI #922/#954」等の表現は当時のスナップショット。**最後に成功確認したソース SHA は `481c76d`（CI #976/#977 SUCCESS）**。その後の source changes には **CI #984/#985 FAILURE**（`GeneralCFGDerivationBridge.lean:50` の `omega`）。コミット `7ff0602` にその修正を push したが、**修正後の CI はこの更新文作成時点で未確認**。必ず GitHub の実際の最新 run と HEAD を調べること。`cor:li-thickness` / `thm:main`(iv) の原稿 v135 完全一致は未宣言。
> 説明・数学的依存・未完了課題・再開プロンプトは上記 Handoff 正本に集約。PR #8 は Draft、Papers/main・v88 は変更しない。

# 【再開用・正本】TCS #1 v128 Lean 形式化 — 2026-10-09 引継書

> **これを次の ChatGPT スレッドで最初に読むこと。最初から作り直さない。**
> 状態は GitHub 実体・CI を最優先。会話の記憶より本書と監査台帳・原稿・実際の Lean ソースを優先する。
> 本書は時点付きスナップショット。再開時は必ず PR HEAD と最新 CI を再確認する。

## 2026-10-09 21:53 JST — verified continuation after CI #954

**Authoritative success point:** CI [#953](https://github.com/growupkuriyama-hub/tcs1-lean-formalization/actions/runs/37915608299) and [#954](https://github.com/growupkuriyama-hub/tcs1-lean-formalization/actions/runs/37915613488) both **SUCCESS** at code commit `0839dca9b0f3279ab7954bee90f0bdd8b663c859`. CI #954 individually passed the v128 delta build, theorem-facing critical path, full `TCS1.All` facade, rejection of `sorry`, and rejection of project-level `axiom`.

**New verified Lean units (do not reconstruct):**

- `V128PositiveWindowKernelForward.lean`: locally trivial positive image implies explicit positive kernel refinement with `n = |h(Σ⁺)|+1`, including positive image/cardinality, idempotent-power/prefix-collision factorization, and a two-idempotent sandwich argument; paired with the previously verified converse in `V128PositiveWindowKernelConverse.lean` to obtain an iff and an existential-window criterion.
- `V128PositiveWindowKernelForward.lean`: upgrade from positive-word kernel refinement to full `RespectsFixedWindowSummary`, plus fixed-window-substitutability transfer and locally trivial concrete-window typing.
- `V128LocallyTrivialThickness.lean`: quantitative characteristic-data/normalization package via the preexisting fixed-window sample and SSBNF bounds. This is a **representation-level theorem conditional on its explicitly listed reduced grammar, short-witness, and normalization hypotheses**; do not call the full manuscript `cor:li-thickness` exact-version-verified until the statement/quantifier audit is complete.

**Status update:** The two previously open positive-window directions are closed in the Lean scope above; the local-triviality/fixed-window class transfer is implemented. CI #954 **does not** establish all 30 v128 manuscript statements as exact matched formulas. The previous 24 R / 3 B / 1 P / 2 O counts were the *pre-closure inventory* and must not be repeated as a fresh current count without reclassifying all 30.

**Next priorities:** (1) audit `prop:li-window` and `cor:li-thickness` against the *current* `Papers/01_fixed-h-cfg/main.tex` and explicitly check empty-language, `h(Σ⁺)`, and effective polynomial/ordinary-thickness quantifiers; (2) finish v116 whole output-generator and `O(n_K^4)` operation-count bridge without confusing size bounds with time; (3) finite-information closure external CFL package; (4) complete 30-statement exact-version audit and `thm:main` packaging. Preserve this draft branch; do not merge PR #8 or edit Papers/main/v88 historical release without authorization.

---

## 2026-10-09 21:53 JST — manuscript-exact li-thickness audit

See [V128_LI_THICKNESS_EXACT_SCOPE_AUDIT_2026-10-09.md](./V128_LI_THICKNESS_EXACT_SCOPE_AUDIT_2026-10-09.md). **CI #957 and #958 SUCCESS** at audit HEAD `ed4c2a77da30c78091cc9e937421ebdf8051b307` after the validated CI #954 code. Current interpretation: `prop:li-window` positive-word equivalence and explicit bound are formally checked; the locally trivial characteristic-data theorem is checked only with explicit SSBNF, short-derivation and normalization bounds **as hypotheses**. The original paper's `cor:li-thickness` and `thm:main`(iv) universally quantify over arbitrary reduced CFGs, so exact-version completion needs a real normalized-grammar bridge and polynomial source-size bounds, not just an envelope. No paper/main/v88 edits. Draft PR remains open.

---

## 0. 再開の一行指示（そのままコピー可）

「GitHub の `growupkuriyama-hub/tcs1-lean-formalization`、Draft PR #8（`audit/tcs1-v128-exact-delta`）にある `START_HERE_TCS1_V128.md` と `FORMALIZATION_TCS1_V128_DELTA.md` を読み、最新 CI を調べ、**v128 の未完了の差分だけ** Lean に実装・CI 修正し、引継書と PR を更新してください。旧版で通った証明を最初からやり直さないでください。」

## 1. GitHub 上の固定した入口

- **形式化リポジトリ**：https://github.com/growupkuriyama-hub/tcs1-lean-formalization
- **作業ブランチ**：`audit/tcs1-v128-exact-delta`
- **Draft PR**：https://github.com/growupkuriyama-hub/tcs1-lean-formalization/pull/8
- **この引継書**：`START_HERE_TCS1_V128.md`（本ブランチのルート）
- **監査台帳**：`FORMALIZATION_TCS1_V128_DELTA.md`
- **統合 Lean facade**：`LeanCfgProject/TCS1/All.lean`
- **論文の真の原稿**：`growupkuriyama-hub/Papers/01_fixed-h-cfg/main.tex`、内部 v128
- **原稿 SHA-256**：`cb18358871d34f6120fed03bc9da7bfed5f1f3095487cca03b07d40ae4d90128`
- **過去の固定済み成果**：v88 Lean tag `tcs1-v88-formalization-3.0.0`、Zenodo DOI `10.5281/zenodo.23120560`。**変更禁止**。

この作業は **PR #8 内の Lean formalization だけ**。TCS の `main.tex`、v88 公開版、main ブランチは許可なく変更しない。

## 2. 2026-10-09 時点の最後の CI 成功点

- **CI #798 SUCCESS** — run `37790263534`。v128 指数的 typed-thickness gap 命題を単一 Lean 定理として完結。
- **CI #818 SUCCESS** — run `37812248496`、commit `eec832f7a0dfefa3d0d422d1a8501c77d4dfa253`。v116 の単項規則バケット列挙と三次候補上界を統合ビルドで検証。
- **CI #824 SUCCESS** — run `37813893036`、commit `371fafb3c62ef8c589c37b3b90f19a67eeee6aa5`。v116 の四次直接出力 **候補記述量 envelope** を統合ビルドで検証。重要：**これは実出力器の四次実行時間の証明ではない**。
- **CI #836 SUCCESS** — run `37818506991`、code commit `d98cf514709bcefbdb6f65ead19498e71311e315`。実有限 (U) 規則集合の sound/complete 一致と `n_K^3` 本数証明、加えて `TCS1.All`、theorem-facing critical path、`sorry` 禁止、独自 `axiom` 禁止の全ゲート通過。
- **CI #858 SUCCESS** — run `37822000555`、code commit `06fe94b6307adee3b62222c0f9a0f35664e85f20`。全 B/U/L/S/epsilon 有限テーブルと、再構成文法の言語等式を統合ビルドで検証。四次実行時間の証明ではない。
- **CI #877 SUCCESS** — run `37826408393`、code commit `d4d61165f950713af141ebec291b5a6ef344f037`。全実 (B) 規則の三カット候補被覆と実規則数 `≤ n_K^3`、統合ビルド、禁止チェックを検証。実行時間の証明ではない。
- **CI #890 SUCCESS** — run `37830187537`、code commit `e7858324859765065598255ac36cb747aff599e8`。計算可能な B ルール語コードの生成器と実有限 B 規則集合の等号、三次の出力本数、統合ビルド・禁止チェックまで検証（時間計算量の証明ではない）。
- **CI #901 SUCCESS** — run `37846653643`、code commit `9605407fefad5bf94b34cd83aa4fd504966e03ac`。v128 原稿30件の Lean 宣言 crosswalk（65個の `#check`）を統合ビルド・禁止チェック付きで検証。未閉鎖の主張は明記して残す。
- **CI #921 SUCCESS** — [run `37885093446`](https://github.com/growupkuriyama-hub/tcs1-lean-formalization/actions/runs/37885093446)、code commit **`4ec6706165aea75fc60d7812ea491b78a524ff50`**。正語上の固定窓 kernel ⇔ 前後境界の型不変性、置換可能性 transfer、および固定窓 kernel refinement ⇒ 正の像の冪等元に関する `e*s*e=e` を証明。先行ビルド、旧 critical path、`TCS1.All`、禁止ゲートはすべて成功。
- **CI #922 SUCCESS** — [run `37885096669`](https://github.com/growupkuriyama-hub/tcs1-lean-formalization/actions/runs/37885096669)、同一 code SHA `4ec6706165aea75fc60d7812ea491b78a524ff50` において全ゲート成功。
- 成功 CI には `TCS1.All` ビルド、theorem-facing critical path、`sorry` 禁止、独自 `axiom` 禁止が含まれる。
- **最新の完全成功は CI #922（同一 code SHA の #921 も成功）**。最後に新しい数学的証明を追加した code SHA は **`4ec6706165aea75fc60d7812ea491b78a524ff50`**。この引継書など**文書のみ**を編集した後の PR HEAD は異なるため、各再開時に最新 HEAD と CI を確認。文書追記後の実行がまだ green でない場合は code SHA #921/#922 と区別する。

## 3. 絶対に捨てない既存の検証済み資産

旧版 v88 までに多項式時間学習構成が Lean で形式化済み。**再構築しない**：

- `ReconstructionComplexityCounts.lean`：`reconstructionSampleNorm`、2カット位置数 `≤ n_K²`、3カット分割位置数 `≤ n_K³`、旧 R2/R3 の pair 空間 `≤ n_K⁴`、旧版の直接出力 envelope `O(n_K⁵)`。
- `ReconstructionFiniteCandidateSpaces.lean`：具体的な有限な2カット・3カット・ペア候補型とその cardinality。
- `ReconstructionFactorSlotState.lean`：`observedReconstructionFactorSlot` と `reconstructionFactorSlotNonterminal_observed`。
- `ReconstructionProductionTables.lean`：旧 representation に対する実際の有限規則テーブル。
- `MaterializedProductionCost.lean`、`MainTheoremMaterializedPackage.lean`：具体的学習器、テーブル、CYK、Gold 同定と既存の多項式仕事量上界。
- `FixedWindowConcreteMonoid.lean`、`FixedWindowExactEquivalence.lean`：固定窓モノイドと Yoshinaka 型 fixed-window substitutability と fixed-h の同値性。

旧版の `O(n_K⁵)` は旧 representation の安全な直接記述上界。v116/v128 では新しい規則構成に対して `O(n_K⁴)` を示す。この **次数の改善だけが差分** であり、「多項式時間で学習できる」という旧版の全体証明を作り直す必要はない。

## 4. v128 で機械検証済みの新しい重要結果

### 4-A. 型付き厚さの指数的ギャップ：完成した原稿命題の具体例

- `V128ThicknessGapFiniteSSBNF.lean`：実際の有限文法 `U,D,E_0,...,E_n`。
- `V128ThicknessGapYieldBound.lean`：trimming 後の `(E_n,1)` からの全生成語が長さ `2^n`、任意の uniform typed `YieldBound` が `≥ 2^n`。
- `V128ThicknessGapOrdinary.lean`：元の ordinary thickness は正確に 1。
- `V128ThicknessGapReducedness.lean`：元文法の productive / reachable。
- `V128ThicknessGapRuleEnumeration.lean`：実規則の sound/complete enumeration、`2n+7`。
- `V128ThicknessGapGrammarSize.lean`：atomic 文法記号のサイズ `≤ 34(n+1)`。
- `V128ThicknessGapProposition.lean`、`V128ThicknessGapClassMembership.lean`：単一の証明済み命題 `v128_exponential_gap_manuscript_instance`、`L(G_n)={a,c}⁺`、固定2元型付け `h_c` で置換可能、ordinary `τ=1` 対 typed `τ≥2^n`。

これは原稿の **`prop:typed-thickness-gap` の明示的 instance** であって、v128 全体の検証済み宣言ではない。ビット単位で添字 `E_i` を印字する別 encoding の主張は含まない。

### 4-B. v116 の新しい substring 文法（言語保存）

- `V128SubstringQuotient.lean`、`V128SubstringCFGPresentation.lean`、`V128FiniteSubstringGrammar.lean` に、v116 の distinct observed factor states、規則 semantics、旧 `BatchLanguage` との言語一致（epsilon を含む）、finite states の二次上界。
- `V128TypedLanguageEquality.lean`、`V128RetainedTypedLanguageEquality.lean` と既存の concrete trim closure で型付き非終端の fibre equality を検証。
- `V128ErasureFlagTyping.lean` は消去単語を扱う product typing の flag 部分を検証。完全な context-free language 逆像閉包は別途検討を要する。

### 4-C. v116 単項規則の三次上界（CI #818 成功）

- `V128SubstringBucketCount.lean`：`SubstringContextBucket H K p q μ`、各バケット `≤ K.card`。
- `V128SubstringBucketEntryBound.lean`：全バケット entry を既存の `ReconstructionFactorSlot K` に単射で写し、総 entry `≤ O(n_K²)`。
- `V128SubstringBucketEnumeration.lean`：既存2カット有限集合から `substringBucketKeys` を image で列挙し、`substringBucketKeys_covers_unary` で **全 `SubstringUnaryRelated` を網羅**。`substringBucketKeys_unaryCandidateCount_le_cube` が無条件の
  `∑_B |B|² ≤ n_K³` を証明。

### 4-D. v116 四次の候補出力 envelope（CI #824 成功）

- `V128SubstringQuarticEnvelope.lean`：
  `substringV116CandidateCount H K ≤ 1+n_K+n_K²+2n_K³ ≤ 4(n_K+1)³`。
  候補1本につき記述長 `≤ n_K+1` を割り当てたときの
  `substringV116DirectOutputBudget H K ≤ 4(n_K+1)⁴`。
  `substringV116WrittenRules_le_quartic` は **実際の出力本数** と **実際の規則記述長** に関する前提を持つ条件付きインターフェース。

## 4-E. v116 の実有限 (U) 規則テーブル（2026-10-09、CI #836 成功）

- **CI #836 SUCCESS** — run `37818506991`、code/head commit `d98cf514709bcefbdb6f65ead19498e71311e315`。新しい `V128SubstringUnaryRuleTable.lean` の単独ビルド、旧 theorem-facing critical path、統合 `TCS1.All`、`sorry`/独自 `axiom` 禁止検査の **すべて成功**。
- `v116UnaryRuleTable` は `substringBucketKeys` の有限な各 context/type bucket 内の ordered factor pairs を (U) production `(x,y)` へ写した具体的な `Finset (Word α × Word α)`。重複は有限集合の image で除去。
- `v116UnaryRuleTable_sound` / `v116UnaryRuleTable_complete` は実テーブルと `SubstringUnaryRelated H K x y` の双方向を証明。`v116UnaryRuleTable_iff` は `finiteSubstringGrammar.unitRule` との完全一致。
- `v116UnaryCandidate_card_eq` および `v116UnaryRuleTable_card_le_cube` は実テーブルの規則数が `reconstructionSampleNorm K ^ 3` 以下であることを、以前に検証済みの cubic bucket theorem から得る。
- **厳密な範囲**：この有限 `Finset` は `noncomputable` な状態/bucket 列挙を用いる。これは (U) の **有限実規則集合の sound/complete + 本数評価** であり、実行可能な serializer、canonical IDs、deduplication の machine step、モノイド値キャッシュ、end-to-end `O(n_K^4)` **実行時間** を証明していない。
- 直前の CI #828 は `release.lean-lang.org` の DNS 名前解決障害による elan setup failure（Lean 自体は未起動）。続く #831 で新規ファイルの Sigma key 射影と `pow_two`/sum の二つの型エラーを検出し、修正。その後の #836 がすべて成功した。
- CI workflow の `Build v128 substring unary delta first` によって、今後は新しい部分だけを先にビルドし、旧版の巨大な critical path を失敗原因探索のために繰り返し待つ必要がない。

## 4-F. v116 の (B)/(U)/(L)/(S)/epsilon 実有限テーブルと言語的正確性（CI #858 成功）

- **CI #858 SUCCESS** — [run `37822000555`](https://github.com/growupkuriyama-hub/tcs1-lean-formalization/actions/runs/37822000555)、code HEAD `06fe94b6307adee3b62222c0f9a0f35664e85f20`。新規モジュール専用ビルド、旧版 theorem-facing critical path、統合 `TCS1.All`、`sorry` と独自 `axiom` 禁止チェックの全項目成功。
- `V128SubstringRemainingRuleTables.lean`：有限観測 factor 状態から (B)/(L)/(S) と epsilon-start の有限 `Finset` を具体化。`v116BinaryRuleTable_iff`、`v116LexicalRuleTable_iff`、`v116StartRuleTable_iff`、`v116EpsilonStartTable_iff`、`v116NonstartEpsilonRule_false`、`v116FourRuleTables_exact` が実テーブルと v116 意味論の完全一致を証明。以前の CI #836 で通過済み (U) 規則テーブルも再利用する。
- `V128SubstringTabulatedGrammar.lean`：`v116TabulatedNonstartGrammar` はテーブル所属述語を直接規則として使う有限型 CFG。`v116TabulatedDerives_to_finiteCFG`、`finiteCFG_to_v116TabulatedDerives` により非終端導出が双方向に一致。`v116TabulatedBatchLanguage_eq_batchLanguage` は **すべての有限標本 K** に対し、(S)/epsilon start を含む構成全体の言語が、既存の検証済み `BatchLanguage H K` と等しいことを保証（空標本と epsilon を含む）。
- この証明は以前の v115→v116 言語保存と v88 の `BatchLanguage` を**再利用**し、旧版の学習器を再実装していない。
- **制限**：この有限テーブルの列挙は `noncomputable`。特に現行 (B) テーブルは観測状態の全三つ組を `Finset.univ.filter` で濾過しており、論文が要求する三カット `O(n_K^3)` **計算可能な候補列挙ではない**。したがって実装の `O(n_K^4)` **実行時間は未検証**であり、`thm:poly-build` の exact-version proof 完了とは呼ばない。
- **次の一手**：既存の `ReconstructionSplitSlot K`（三カット有限型）から (B) 規則を sound/complete に列挙し、既存 `reconstructionSplitSlot_card_le_cube` をそのまま使って三次の出力候補上界を得る。(L)/(S) も有限候補を直接走査する計算可能な表現へ橋渡しし、canonical factor/context IDs、`h` cache、dedup、規則の文字列 encoder と step-count を結ぶ。
- 初回 CI #849 で epsilon 表への所属補題のみ未解決。空語が K に属する場合分けで修正し、#858 で正式検証。

## 4-G. (B) 実規則数の三次上界を三カットへ接続（CI #877 成功）

- **CI #877 SUCCESS** — [run `37826408393`](https://github.com/growupkuriyama-hub/tcs1-lean-formalization/actions/runs/37826408393)、**Lean コード SHA `d4d61165f950713af141ebec291b5a6ef344f037`**。新規モジュール先行ビルド・既存重要定理群・`TCS1.All`・`sorry`/独自 `axiom` 禁止の全ゲート成功。
- **新規ファイル**：`LeanCfgProject/TCS1/V128SubstringBinarySplitSlots.lean`。旧版で検証済みの `ReconstructionSplitSlot K`（標本語と三つの切断位置）から `v116BinarySplitCode` で (親, 左子, 右子) の**候補語**を復号。`v116BinarySplitCodes_cover` は実際の v116 (B) 規則すべてがこの候補の像に入ることを証明する。
- **新しい定理**：`v116BinarySplitCodes_card_le_cube` により三カット候補語集合の濃度 `≤ (reconstructionSampleNorm K)^3`。さらに `v116BinaryProductionWordCode_injective`、`v116ActualBinaryRule_has_split_slot`、`v116ActualBinaryRuleToSplitSlot_injective` で**実際の** `v116BinaryRuleTable K` の各規則から三カットスロットへの単射を構成し、`v116BinaryRuleTable_card_le_cube` により **実 (B) 規則数** `≤ n_K^3` を無条件に証明した。
- 新しい証明は前回 CI #858 の全 B/U/L/S/epsilon 有限規則テーブルと言語等式、CI #836 の U 規則三次本数上界、およびさらに前の三カット cardinality 補題を再利用。古い v88 を作り直していない。
- **注意すべき限界**：`v116BinarySplitCodes` の生の候補集合は反転・空部分など無効候補を含み得るため、**そのすべてを (B) として出力してよいわけではない**。実規則から代表スロットへの単射には `Classical.choose` を用いる。現在の `v116BinaryRuleTable` も `noncomputable` な三状態全組のフィルタに基づく。したがって**三次の実規則数上界は Lean で完了したが、三次で走る有効な (B) 規則列挙器と四次の全構築 step-count は未完**。
- 初回 #869 は親 factor の `take` と切断長の正規化が未解決。#873 は List prefix と Finset membership の補題指定が必要だった。#875 で残った List prefix の証明に `List.take_append_length` を明示し、#877 が green となった。

## 4-H. 計算可能な (B) 規則語テーブルと実テーブルの完全一致（CI #890 成功）

- **CI #890 SUCCESS** — [run `37830187537`](https://github.com/growupkuriyama-hub/tcs1-lean-formalization/actions/runs/37830187537)、最後の検証済み **Lean code commit `e7858324859765065598255ac36cb747aff599e8`**。新規モジュール専用ビルド、既存 theorem-facing critical path、`TCS1.All`、`sorry`/独自 `axiom` 禁止チェックの全ゲート成功。
- **新規ファイル**：`V128SubstringEffectiveBinaryTable.lean`。`noncomputable` 指定のない `def` として、①二カット `ReconstructionFactorSlot K` を走査し標本内の**非空観測部分語**を有限集合へ列挙（`v116EffectiveObservedFactorWords`）、②既存の三カット `ReconstructionSplitSlot K` を `v116BinarySplitCode` で復号（`v116EffectiveRawBinaryCodes`）、③語の連結条件、左右の非空条件、親語の標本内出現を判定して `Finset.filter` する `v116EffectiveBinaryWordTable` を定義した。
- `v116EffectiveObservedFactorWords_iff` が二カット観測テーブルの sound/complete、`v116EffectiveBinaryWordTable_iff` が実行可能な (B) テーブルの**正しい規則条件**との双方向対応を証明。**`v116EffectiveBinaryWordTable_eq_actual`** は計算可能な語コードの集合と、CI #858 で認証済みの非計算的・証明付き状態の `v116BinaryRuleTable K` を `v116BinaryProductionWordCode` で写した集合との**厳密な等号**である。
- `v116EffectiveBinaryWordTable_card_le_cube` はフィルタされた実出力の種類数 `≤ (reconstructionSampleNorm K)^3` を、CI #877 で検証済みの三カット候補数上界から得る。既存の (U) テーブル三次上界もそのまま維持される。
- **限界**：これは Lean 上の**実行可能な有限 `Finset` 定義と extensional correctness** の検証である。二カット観測テーブルをフィルタのたびに再計算しないための明示的キャッシュ、`Finset.image/filter` の単語比較／重複除去のマシンステップ数、正規化済み状態 ID、型値 `h` のキャッシュ、U/L/S/epsilon の有効出力器、文字列 serializer、end-to-end `O(n_K^4)` 時間は**まだ証明していない**。有限出力個数が三次であるだけでは四次実行時間を意味しない。
- **次に行うこと**：二カット部分語集合を一度だけ前処理する構成へ移し、三カット走査と妥当性判定を評価するコストモデルを用意する。候補語の**リスト出力で重複を許す仕様**も検討し、意味論的には同一の規則が重複しても構わないことを利用できるか検証する。出力表現を確定してから、(U) バケット、(L)/(S)/epsilon、型値キャッシュ、符号化長・書字ステップを結ぶ。TCS 原稿 `thm:poly-build` の O(n_K^4) 説明との**正確な**対応を監査する。
- CI #887 は `Observed` と `List.append_assoc` の書き換え3箇所で失敗。#888 は連結の左右括弧の差2箇所を検出。修正後の #890 は完全成功した。

## 4-I. v128 番号付き30件の一対一監査（CI #901 成功）

- **監査表の正本**：[`V128_NUMBERED_CLAIMS_ONE_TO_ONE_AUDIT_2026-10-09.md`](./V128_NUMBERED_CLAIMS_ONE_TO_ONE_AUDIT_2026-10-09.md)。`Papers/01_fixed-h-cfg/main.tex` 内の番号付き `theorem/proposition/lemma/corollary` **30件すべて**（ラベルのない1636行の系も含む）を原稿順に列挙し、各項目に旧 v79/v88 または現行 v128 の具体的 Lean 定理名と未完了の差分を対応させた。
- **Lean 側の照合索引**：`LeanCfgProject/TCS1/V128ThirtyClaimCrosswalk.lean`。30個の見出しと **65個の `#check`**。未閉鎖の命題は明示的に OPEN と記載し、`True` の成功マーカーで完了を偽装していない。
- **CI #901 SUCCESS** — [run `37846653643`](https://github.com/growupkuriyama-hub/tcs1-lean-formalization/actions/runs/37846653643)、**Lean code SHA `9605407fefad5bf94b34cd83aa4fd504966e03ac`**。v128 delta 先行ビルド、旧定理群、`TCS1.All`、`sorry`/独自 `axiom` 禁止チェックすべて成功。これは旧定理参照先の**存在と型検査の検証**であり、未完の v128 原稿命題を証明したことを意味しない。前回 CI #890 の計算可能 B テーブルの定理もそのまま成功。
- **30件の監査分類**：**既存 Lean 数学的証明の再利用先あり R=24、橋渡し B=3（`thm:main`、`cor:ilt`、`thm:poly-build`）、部分 P=1（`prop:finite-info-closure` の RS 側は証明済み、CFL 閉包は古典的外部事実）、未閉鎖 O=2（`prop:li-window`、`cor:li-thickness`）**。
- **重要な方針修正**：旧 `MaterializedProductionCost.lean` と `MainTheoremMaterializedPackage.lean` は実行可能なパーサ・学習器と多項式の**組合せ的操作数評価**まで既に機械検証している。v128 の規則構成と厳密四次評価への接続は必要だが、論文で約束していない Lean evaluator/CPU の1命令単位 semantics を新しい必須検証基準として上乗せしない。**原稿の「多項式時間」の定理文と証明本文の「四次時間」の具体的評価は区別する**。
- **本当に優先する新規数学的証明**：`prop:li-window` が述べる locally trivial positive-image の fixed-window kernel refinement criterion（明示 `(n,n)`、局所自明性、類の union）。原稿中の Pin 2025 に依存する補題を境界として明示し、既存の固定窓 typing / refinement theorem を再利用。次に `cor:li-thickness` の retained typed language / trimming / thickness bridge を証明する。古い Gold learner、規則、固定窓の section 7 を再実装しない。
- **注意**：R=24 は各 v128 主張について再利用可能な非自明な Lean 定理が確認できたという意味。30件すべてが manuscript-exact に一対一の定理文で formal proof complete になったという意味ではない。行ごとの最終的な hypothesis/conclusion の全称量化・境界チェックは別途監査対象。

## 4-J. 正の像の局所自明性への逆向き（CI #921/#922 成功）

**今までの会話の要約ではなく、実際に GitHub ソースが CI green になった到達点。**

- `LeanCfgProject/TCS1/V128PositiveWindowKernel.lean`：
  - `PositiveWindowKernelRefines` を **正語 `Σ⁺` のみ**における `ker(h_{k,ℓ}) ⊆ ker(h)` として定義。空語を混ぜない。
  - `PositiveWindowBoundaryInvariant` は、長さ `k` の prefix と長さ `ℓ` の suffix を固定して正語同士を比較した際の `h`-type 不変性。
  - `positiveWindowKernelRefines_iff_boundary` はその **同値**を既存の実 `fixedWindowMonoidHom` に対して形式化。窓 `(0,0)` も含む。
  - `fixedHSubstitutable_of_positiveWindowKernelRefines`、`fixedWindowSubstitutable_of_positiveWindowKernelRefines` は、すでにある refinement と Yoshinaka 固定窓対応を利用して **RS クラス側の移送**を証明。
- `LeanCfgProject/TCS1/V128PositiveWindowKernelConverse.lean`：
  - `v128RepeatWord`、`v128RepeatWord_length_lower`、`v128RepeatWord_type_succ` で冪等元を表す非空語を十分な長さに繰り返す。
  - `v128FixedWindow_long_frame_middle_independent` で、長い左右の `p,q` の間に挟んだ中央の語は固定窓 summary から見えないことを証明。
  - `positiveWindowKernel_refines_implies_idempotent_sandwich` が、非空語 `r` の像 `e=h(r)` が冪等なら任意の中央語 `z` に対し `h(r z r)=h(r)`、すなわち `e*h(z)*e=e` を証明。
  - `PositiveImageSandwichTrivial`、`positiveWindowKernel_refines_implies_positiveImageTrivial` により **固定窓 refinement ⇒ 正の像 `h(Σ⁺)` の局所自明性（冪等元 sandwich identity）**を完結。
- **Lean CI #921 と #922** はともに **SUCCESS**、code SHA **`4ec6706165aea75fc60d7812ea491b78a524ff50`**。旧 theorem-facing critical path、`TCS1.All`、`sorry`・プロジェクト `axiom` 禁止を含めて green。
- **未証明を隠さない**：v128 `prop:li-window` の逆ではないほう、すなわち **「正の像が locally trivial ⇒ 明示 `n=|h(Σ⁺)|+1` による `(n,n)` 固定窓の正語 kernel refinement」**はまだ証明していない。Pin (2025) の有限半群分解 `S^n=S E(S) S` および `e s f=e f` の使用・実装が次の数学的核心。固定窓 `h_{k,ℓ}` 自身の正の像の局所自明性、クラス等式 `KL=∪RS_h` と CFL 版も、**この一方向が通っただけではすべては終了しない**。
- `cor:li-thickness`、`thm:main` (iv) は引き続き **未閉鎖**。旧 `V83TypedThicknessWitnessBounds`、`V128RetainedTypedLanguageEquality`、`V128TypedTrimSuccessfulBranch`、Proposition 7.4 normalization、旧 fixed-window bound を再利用して仕上げる。

### 4-J 関連のドキュメント

- [30件の一対一対応表](./V128_NUMBERED_CLAIMS_ONE_TO_ONE_AUDIT_2026-10-09.md) — R=24 / B=3 / P=1 / O=2（**区分は維持**：#5 は一方向のみ前進し、まだ完結していない）。
- [v128 詳細監査台帳](./FORMALIZATION_TCS1_V128_DELTA.md)。
- [Issues #9](https://github.com/growupkuriyama-hub/tcs1-lean-formalization/issues/9) と [Draft PR #8](https://github.com/growupkuriyama-hub/tcs1-lean-formalization/pull/8)。

## 5. まだ完了していないこと（最優先順）

1. **`prop:li-window` の残る順方向（最優先の数学的差分）**：局所自明な正の像 semigroup から具体的に `(n,n)`（`n=|h(Σ⁺)|+1`）の正語 kernel refinement を証明。**反対方向の sandwich identity は CI #922 で完了**、再証明しない。Pin 2025 の `S^n = S E(S) S` および `e s f = e f` を正確に取り込む。窓 typing の正の像自体の局所自明性と `KL=⋃RS_h`（CFL 版を含む）まで原稿に合わせて扱う。
2. **`cor:li-thickness` と主定理 (iv)**：上記 kernel-refinement と既存の retained typed fibre 言語等式、successful-branch trimming、fixed-window typed-yield bound、thickness-preserving SSBNF normalization、特性標本 bound を結合。学習器・固定窓旧証明を作り直さない。
3. **v116 `thm:poly-build` への橋渡し**：旧版の実行可能 CYK/学習器と多項式 scan/comparison envelope は検証済み。新 v116 の意味論・実有限規則表・有効 (B) 表・B/U の三次本数・候補出力四次 envelope も検証済み。残る `(U)/(L)/(S)/epsilon` 有効構築、識別子・キャッシュ・重複処理を含む `O(n_K^4)` の**論文レベルの演算回数 accounting**。低レベル CPU/Lean evaluator の instruction semantics は必須にしない。「三次候補数」≠「実行時間四次」を明記。
4. **`prop:finite-info-closure` 全体**：固定型 RS 側 (i)/(ii)/(iii) は Lean で検証済みだが、(ii) regular-filtered CFL と (iii) erasing inverse-image CFL の伝統的閉包定理を `\mathcal C_h` 結論に明示的に接続する Lean package は未確認。数学的には古典的な外部事実であり、新規主張と取り違えない。
5. **`thm:main` (i)/(iii)・`cor:ilt` の v116 packaging と厳密照合**：既存の Gold/学習器/BatchLanguage を使い、`v116TabulatedBatchLanguage_eq_batchLanguage` による新版の意味論保存を各 stage で接続。
6. **原稿 v128 の exact-version 最終監査**：番号付き環境 **30件の対応先特定と Lean `#check` 65件の green は CI #901** で完了。しかし *manuscript-exact* な全仮定/結論/全称量化の一致、番号なしの重要主張、依存境界は未了。既存の v88 audit `True` marker を全文証明と混同しない。

**進捗の数え方**：30件中 **24件 R（旧/現行 Lean 数学的証明を再利用できる）・3件 B（接続が要る）・1件 P（部分証明）・2件 O（主張全体は未閉鎖）**。これは「全体の80%が formal proof complete」と言っているのではなく、**30件のうち80%の項目に再利用可能な既存の proof source がある**という監査上の意味。30件の対応表作成は **30/30 完了**、v128 exact-version 完全形式化のパーセンテージは未確定。

## 6. 再開手順（今後の ChatGPT の作業用）

1. GitHub ツールで **PR #8 の最新 HEAD と Draft 状態を確認**。
2. 最新 HEAD の Actions run を取得し、最終成功／失敗を確定。失敗なら `fetch_workflow_run_jobs` → `fetch_workflow_job_logs` で具体的な `error: LeanCfgProject/TCS1/... ` 行を抽出する。
3. `START_HERE_TCS1_V128.md` と `FORMALIZATION_TCS1_V128_DELTA.md`、最新 Lean ソースと `Papers/01_fixed-h-cfg/main.tex` を読む。
4. **未完の差分だけ**実装。重複する旧版定理の再実装は禁止。変更は `audit/tcs1-v128-exact-delta` への commit に限定し、`All.lean` を更新する。
5. CI が green になって初めて「機械検証済み」と報告し、**この引継書を更新する**。検証待ちなら保留として明記。
6. PR を勝手に merge しない。投稿 TCS 論文や v88 の正式版を勝手に改変しない。

## 7. 再開を楽にする短いプロンプト

> 「博士論文統合プロジェクトの TCS #1 **v128** Lean 形式化を続けてください。最初に GitHub `growupkuriyama-hub/tcs1-lean-formalization` の **Draft PR #8**（`audit/tcs1-v128-exact-delta`）の `START_HERE_TCS1_V128.md` と `FORMALIZATION_TCS1_V128_DELTA.md`、30件の一対一監査表を読み、HEAD と最新 CI を確認してください。**CI #921/#922**（code SHA `4ec6706165aea75fc60d7812ea491b78a524ff50`）で `prop:li-window` の **固定窓 kernel ⇒ 局所自明性**は証明済みです。**逆方向『局所自明性 ⇒ 明示 (n,n) 固定窓の kernel refinement』** の未証明部分から進め、次に `cor:li-thickness` を旧版の typed-yield/normalization を使って接続してください。旧 v88 定理や CYK/学習器を作り直さず、Lean を PR ブランチへ push → CI green 確認 → 本引継書と Issue #9 更新まで行ってください。原稿 `Papers/01_fixed-h-cfg/main.tex`、main、v88 リリースは編集・merge しないでください。」

**本書は GitHub に永続化した作業履歴の入口です。チャット履歴の保存・圧縮に依存しません。**

