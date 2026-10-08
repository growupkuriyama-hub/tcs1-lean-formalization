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
- **CI #836 SUCCESS** — run `37818506991`、code commit `d98cf514709bcefbdb6f65ead19498e71311e315`。実有限 (U) 規則集合の sound/complete 一致と `n_K^3` 本数証明、加えて `TCS1.All`、theorem-facing critical path、`sorry` 禁止、独自 `axiom` 禁止の全ゲート通過。
- **CI #858 SUCCESS** — run `37822000555`、code commit `06fe94b6307adee3b62222c0f9a0f35664e85f20`。全 B/U/L/S/epsilon 有限テーブルと、再構成文法の言語等式を統合ビルドで検証。四次実行時間の証明ではない。
- **CI #877 SUCCESS** — run `37826408393`、code commit `d4d61165f950713af141ebec291b5a6ef344f037`。全実 (B) 規則の三カット候補被覆と実規則数 `≤ n_K^3`、統合ビルド、禁止チェックを検証。実行時間の証明ではない。
- **CI #890 SUCCESS** — run `37830187537`、code commit `e7858324859765065598255ac36cb747aff599e8`。計算可能な B ルール語コードの生成器と実有限 B 規則集合の等号、三次の出力本数、統合ビルド・禁止チェックまで検証（時間計算量の証明ではない）。
- **CI #901 SUCCESS** — run `37846653643`、code commit `9605407fefad5bf94b34cd83aa4fd504966e03ac`。v128 原稿30件の Lean 宣言 crosswalk（65個の `#check`）を統合ビルド・禁止チェック付きで検証。未閉鎖の主張は明記して残す。
- 成功 CI には `TCS1.All` ビルド、theorem-facing critical path、`sorry` 禁止、独自 `axiom` 禁止が含まれる。
- **コードの最後の完全成功は CI #901（監査索引の統合）**。旧数学的内容を直接追加した直近 checkpoint は CI #890。 文書のみを追加した後の HEAD はこのコード commit と異なる（引継書・監査文書を更新した時点で別の CI が走る）。必ず最新 HEAD と latest CI を確認。

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

## 5. まだ完了していないこと（最優先順）

1. **v116 の実行可能な出力器・四次時間証明との橋渡し**：非計算的な全 (B)/(U)/(L)/(S)/epsilon 有限テーブルの意味論的正確性は CI #858 済み。(B) 実規則の三カット候補被覆と三次本数上界は CI #877 で完了。**計算可能な (B) 有効性フィルタと実規則集合への正確な出力接続は CI #890 で完了**。次は二カット集合のキャッシュと列挙器の machine-step 証明を設計し、(L)/(S)/epsilon・(U) を計算可能な索引と結ぶ。canonical factor/context ID、出力エンコーダ、構築・dedup・型計算の step-count を実証する。候補計数の三次と記述量の四次が Lean を通っていても、実出力アルゴリズム全体が `O(n_K⁴)` 時間で実行可能と確認したことには **ならない**。
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

> 「博士論文統合プロジェクトの TCS #1 Lean 形式化を、GitHub PR #8 の `START_HERE_TCS1_V128.md` から再開してください。最新 CI を確認し、v116 実出力器の O(n_K^4) 証明へ進めてください。完了済みの v88 構成と CI #901 までの監査と既存証明をやり直さず、コードを実際に push・CI 確認・引継書更新まで実行してください。」

**本書は GitHub に永続化した作業履歴の入口です。チャット履歴の保存・圧縮に依存しません。**

