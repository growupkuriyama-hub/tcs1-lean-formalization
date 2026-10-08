# 【再開用・正本】TCS #1 v128 Lean 形式化 — 2026-10-09 引継書

> **これを次の ChatGPT スレッドで最初に読むこと。最初から作り直さない。**
> 状態は GitHub 実体・CI を最優先。会話の記憶より本書と監査台帳・原稿・実際の Lean ソースを優先する。
> 本書は時点付きスナップショット。再開時は必ず PR HEAD と最新 CI を再確認する。

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
- 成功 CI には `TCS1.All` ビルド、theorem-facing critical path、`sorry` 禁止、独自 `axiom` 禁止が含まれる。
- この引継書やその他の Markdown を追加した後の新しい HEAD は CI #824 の commit と異なり得る。再開時は CI を再確認。

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

## 5. まだ完了していないこと（最優先順）

1. **v116 の残りの実出力器との橋渡し**：`finiteSubstringGrammar` の (B)/(L)/(S)/epsilon の実際の有限規則テーブル（(U) の非計算的 Finset は CI #836 済み）、候補との sound/complete 対応、規則の書字コスト（または canonical ID）、構築・dedup・型計算の step-count。候補計数の三次と記述量の四次が Lean を通っていても、実出力アルゴリズム全体が `O(n_K⁴)` 時間で実行可能と確認したことには **ならない**。
2. **`prop:li-window`**：有限モノイドの正の像 semigroup が locally trivial ⇔ ある finite-window `h_(k,l)` の kernel が `ker h` を（正語上で）refine。古い fixed-window の基礎定理と区別し、新命題を直接形式化する。既存証明と原稿の正確な定義・既往文献帰属を必ず照合。
3. 上記からの characteristic-data corollary と `prop:finite-info-closure` の **完全な CFL closure 側** の義務。
4. v128 の全30個の theorem/proposition/lemma/corollary environment と Lean 宣言の exact correspondence（旧版の audit `True` marker を v128 の完全証明と誤認しない）。

## 6. 再開手順（今後の ChatGPT の作業用）

1. GitHub ツールで **PR #8 の最新 HEAD と Draft 状態を確認**。
2. 最新 HEAD の Actions run を取得し、最終成功／失敗を確定。失敗なら `fetch_workflow_run_jobs` → `fetch_workflow_job_logs` で具体的な `error: LeanCfgProject/TCS1/... ` 行を抽出する。
3. `START_HERE_TCS1_V128.md` と `FORMALIZATION_TCS1_V128_DELTA.md`、最新 Lean ソースと `Papers/01_fixed-h-cfg/main.tex` を読む。
4. **未完の差分だけ**実装。重複する旧版定理の再実装は禁止。変更は `audit/tcs1-v128-exact-delta` への commit に限定し、`All.lean` を更新する。
5. CI が green になって初めて「機械検証済み」と報告し、**この引継書を更新する**。検証待ちなら保留として明記。
6. PR を勝手に merge しない。投稿 TCS 論文や v88 の正式版を勝手に改変しない。

## 7. 再開を楽にする短いプロンプト

> 「博士論文統合プロジェクトの TCS #1 Lean 形式化を、GitHub PR #8 の `START_HERE_TCS1_V128.md` から再開してください。最新 CI を確認し、v116 実出力器の O(n_K^4) 証明へ進めてください。完了済みの v88 構成と CI #824 までの証明をやり直さず、コードを実際に push・CI 確認・引継書更新まで実行してください。」

**本書は GitHub に永続化した作業履歴の入口です。チャット履歴の保存・圧縮に依存しません。**

