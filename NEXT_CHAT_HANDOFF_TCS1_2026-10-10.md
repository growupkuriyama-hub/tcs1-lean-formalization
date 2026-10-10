# 【最優先・再開用】TCS #1 Lean 形式化 引継ぎ — 2026-10-10 夜（Claude セッション 3）

> **この節が最新。** 下の「セッション 2」以降は履歴。再開手順：**この節 → GitHub の実 HEAD と最新 Actions（annotations API）→ 実際の Lean ファイル → `Papers/01_fixed-h-cfg/main.tex`（現在 v148）**。

## A. 状態（GitHub Actions の実結果）

| 項目 | 値 |
|---|---|
| ブランチ / PR | `audit/tcs1-v128-exact-delta` / Draft PR #8（merge・Ready 化していない） |
| **最後に GREEN を確認したコード SHA** | **`313aa04c95a16d09ccc5c7ead3d62ae0d1f5a715` — CI [#1040](https://github.com/growupkuriyama-hub/tcs1-lean-formalization/actions/runs/38044662069) SUCCESS（5 ゲートすべて、V144 の `#guard_msgs` 公理監査と `#guard` 実行例を含む）** |
| 新規定理を初めて検証した CI | `315f25a` CI [#1036](https://github.com/growupkuriyama-hub/tcs1-lean-formalization/actions/runs/38042988338)（5 ゲートすべて成功） |
| 本セッション初回の GREEN | `bed41c3` CI #1028（Horn エンジン＋正規化器本体） |
| 前セッション最後の GREEN | `a27fa38` CI #1024 |
| 原稿 | 依頼時点 v144（sha256 `d9c23a41…`）→ 現在の Papers `main` は **v148**（`04994e0`、sha256 `824fc84a…`）。照合は両方に対して実施 |

## B. 本セッションで CI 検証された定理

**`prop:thick-ssbnf-normal` の多項式時間（第一目標）**
- `V144HornClosure.lean`：歩数付き Horn 閉包エンジン `hornC`。正しさ `mem_hornC_iff`、歩数 `hornC_cost_le`（`8(|dom|+1)²(|rules|+Σ|body|+1)(E+1)`）。
- `V144SSBNFNormalizer.lean`：付録の順序どおりの実行可能な正規化器 `normalizeTrace`。順序は nullable、二分化後の ε 除去（二項規則ごとに変種 3 個以下、2^k 列挙なし）、unit 閉包、unit 除去、productive、reachable、出力。各段の値の仕様と歩数を証明し、全体で `normalizeTrace_steps_le`（`≤ 400(m+1)^5(E+1)`）。
- `V144SSBNFBridge.lean`：計算したリストが既存の意味論的定義（`BinaryNullable`、`EpsilonElimUnitRule`、`UnitReach`、`UnitFree*`、`ProductiveUnitFreeReachable`、`reducedSSBNF*`）と**完全に一致**することを証明。書かれた文法の導出と既存の縮約文法の導出も一致する（`codeDerives_iff`、`codeStartLanguage_eq`、到達性 `out_reachable`）。
- `V144SSBNFFrontEnd.lean`：明示リストからの前処理。wrapper による終端分離と、suffix 状態（入力右辺の尾部へのポインタ）による二分化。`frontEndBinaryGrammar` の規則を明示的に特徴づけ、サイズ・比較コスト・線形時間 `frontCodeC_snd_le` を証明。
- `V144SSBNFNormalize.lean`：`normalizeSSBNF`。`codeMatches_indexed`（前処理の出力が既存の `indexedFiniteFrontEndGrammar G` と完全に一致）、`inputScale_eq_normalizationScale`、**`normalizeSSBNF_steps_le`：`≤ 900(n+1)^6` 歩**。
  - **紙面対応 `prop_thickSSBNFNormal_executable`**：次の 5 点を示す。
    1. 言語 = `L(G,A)`
    2. 既存の縮約 SSBNF 文法 `Nf` と非終端記号・規則が完全に一致
    3. 異なる要素の数が `indexedSSBNFGrammarSizeEnvelope n` 以下、書かれたリスト長が `n`／`n³`
    4. すべての非終端記号が到達可能で、`1 + n²·thicknessBar τR` 以下の長さの語を導出する
    5. 時間 `900(n+1)^6`
  - `prop_thickSSBNFNormal_executable_degenerate`：非空の語がない場合も正しく、すべての入力で正しい。
- `V144SSBNFExample.lean`：`S → aSb | ε` でコンパイル済みの正規化器を実行し、`#guard` で確認（非終端記号 4、終端規則 3、二項規則 2、ε フラグ、4313 歩）。
- 計算モデル：V135 と同じく、値と歩数を同じ再帰で計算する。suffix 状態の比較はセル単位、記号の比較は 1 歩（word-RAM）。`Finset` は証明の中でだけ使い、アルゴリズムでは使わない。詳細は `V144_SSBNF_NORMALIZATION_TIME_AUDIT.md`。

**v144–v148 監査（第二目標）**：`V144_NUMBERED_CLAIMS_CROSSWALK.md`
- 機械的な差分（v135／v144／v148）：主張文が変わったのは `prop:linear-separator-example` だけ。証明が変わったのは #3、#5、#12、#23、#24。
- `prop:linear-separator-example`（∃h 形）：`prop_linearSeparatorExample_existsH`（`V144LinearSeparatorExists.lean`）。既存の `lpm_proposition86_full_semantic` から ∃ の証人を与えた。
- `thm:poly-build`（v141 の直接列挙）：`constructV116C` と同じ O(n³) 候補 × O(n) で、重複除去なし。整合する。
- `prop:nonlinear-rs-example`：主張は不変。**「決定性文脈自由」の節は Lean で形式化されていない**（DPDA モデルがない）ため R から **P** に再評価した。
- 集計：F=8（#2, #4, #5, #11, #12, #18, #19, #23）、R=21、P=1（#24）。

**公理監査**：`V144AxiomAudit.lean`（`#guard_msgs`、上記の紙面対応 4 定理）。

## C. CI で修正した失敗（annotations で確認）

- `3ba1980` CI #1030：Bridge の `cases` で変数が消えた、`EpsilonElimUnitRule` の場合分けの名前の数。`Prod.mk.inj` と `subst`、補題 `epsElim_cases` で修正。
- `225c096` CI #1032：FrontEnd の `simp` が `Sum.exists` で展開しすぎた、`generalize` がゴールにも及んだ。ローカルの mock で再現して修正（`7c2e016`）。
- `7c2e016` CI #1034：Normalize の `obtain` の再利用、`include L`、構造体リテラルの修正。`315f25a` CI #1036 で GREEN。

## D. 残る課題（未証明）

1. `prop:nonlinear-rs-example` の DCFL 節：DPDA の形式化がない。
2. 学習器の 1 更新あたりのコスト：`cor:ilt`／`thm:main`(iii) の更新は所属判定（table-backed CYK）と標本リスト（`Finset.toList`）を含むが、v116 表現での歩数は未計上。次の補題は、歩数付き CYK を v116 文法コードの上に実装し、`codeLanguage` との一致と多項式歩数を示すこと。
3. 正規化の次数（6）は最適化していない。書いたリストは重複を許す（異なる要素の数は既存の上界で抑えられる）。
4. 計算量は RAM／ポインタ機械の操作数である。ビット計算量や実機の時間ではない。

## E. 次回の最初の作業

1. HEAD の CI を確認する（`gh run list` と annotations API）。
2. D-2：歩数付き CYK 所属判定と、学習器 1 更新の歩数。
3. （任意）D-1：DPDA の定義と Δ* の受理。

## F. 変更・追加したファイル（本セッション）

- 新規 Lean：`V144HornClosure`、`V144SSBNFNormalizer`、`V144SSBNFBridge`、`V144SSBNFFrontEnd`、`V144SSBNFNormalize`、`V144LinearSeparatorExists`、`V144SSBNFExample`、`V144AxiomAudit`
- 変更：`All.lean`（import の追加のみ）
- 文書：本書、`START_HERE`、`DELTA` の冒頭、新規 `V144_SSBNF_NORMALIZATION_TIME_AUDIT.md`、`V144_NUMBERED_CLAIMS_CROSSWALK.md`

## G. 変更禁止（従来どおり）

`Papers`、TCS 投稿版、形式化の `main`、v88、PR #8 の merge・Ready 化、force push。

---

# 【最優先・再開用】TCS #1 Lean 形式化 引継ぎ — 2026-10-10 夜（Claude セッション 2）

> **この節が最新。** 下の「午後更新」「午前版」は履歴。再開手順：**この節 → GitHub の実 HEAD と最新 Actions（annotations API）→ 実際の Lean ファイル → `Papers/01_fixed-h-cfg/main.tex`(v135)**。

## A. 状態の要約（GitHub Actions の実結果）

| 項目 | 値 |
|---|---|
| ブランチ / PR | `audit/tcs1-v128-exact-delta` / Draft PR #8（未 merge・Draft のまま） |
| **最後に GREEN を確認したコード SHA** | **`a27fa38b07139da6fd5d3d8300424bc5107b18f0` — CI [#1024](https://github.com/growupkuriyama-hub/tcs1-lean-formalization/actions/runs/38030781856) SUCCESS（5 ゲートすべて、`#guard_msgs` 公理監査を含む）** |
| 本セッションのその他の GREEN | `64cc480` CI #1022（(iii)・(v)・cor:ilt）、`b7e8c45` CI #1016（thm:poly-build） |
| 前セッション最後の GREEN | `d130c3d` CI #1008、文書 HEAD `1ea5bbe` CI #1010/#1011 |
| 原稿 | v135、sha256 `e8590799…`（Papers `2e67f3a`） |

## B. 本セッションで新たに CI 検証された定理

**`thm:poly-build`（第一目標）** — `V135CostedPrimitives.lean`、`V135PolyBuildAlgorithm.lean`、`V135PolyBuildBridge.lean`（CI #1016）
- **計算モデル**（ファイル冒頭に明記）：値と歩数を同じ再帰で計算。連結リストのセル訪問・生成、文字等価、文字型参照と有限モノイド演算・等価、添字比較、ループ 1 回、出力 append のセルを単位とする。`Finset` 操作・ハッシュ・ソートは不使用。任意長文字列比較を定数とはしない（文字単位で課金）。
- `constructV116C`：実行可能な構成器。因子を**そのまま名前として**書く（原稿の証明が許す方式。ID もハッシュも不要）。(B)・(U)・(L)・(S)・ε・非終端記号をすべて出力。重複行は残る。
- **定理 A**：`mem_binary`・`mem_unary`・`mem_lexical`・`mem_start`・`epsilon_iff`・`mem_nonterminals`、既存表への接続 `constructV116H_*_iff`（`v116EffectiveBinaryWordTable`＝実 (B) 表、`v116UnaryRuleTable`、(L)(S)(ε) 表）。
- **定理 B**：`constructV116H_language`。書かれた文法を名前どおりの CFG と読んだ言語が `BatchLanguage H K` と一致。
- **定理 C**：`constructV116Cost_le`（≤ `1400·(N+1)^4`、`N = Σ(|w|+1)`）、`constructV116HCost_le`（重複なしの列なら `N = ‖K‖`）。
- 紙面対応：`PolyBuild.thm_polyBuild`。公理は `#guard_msgs` で標準3公理のみと強制。
- `#eval` で具体例 `K={ab,b}` の出力を確認済み。
- 監査文書：`V135_POLY_BUILD_COMPLEXITY_AUDIT.md`。**四次時間をこの計算モデルで証明済み。**

**`prop:finite-info-closure` (iii) の CFL 側** — `V135InverseHomTransducer.lean`、`V135InverseHomCFL.lean`、`V135InverseHomFinite.lean`（CI #1022）
- 文字位置トランスデューサ（境界から境界への run ＝ 非消去文字語の逆像）。状態で精密化した文法、消去文字の挿入文法、両者の合成で `{y | φ(y) ∈ L}` を正確に生成。
- 有効状態への制限、有限性、汎用補題「右辺長有界 ⇒ 有限 `IndexedMixedCFG`」。
- `InverseHom.cfl_inverseImage`：**消去的準同型を含む**一般の `φ` について、明示的な有限 CFG で逆像を生成。
- `InverseHom.finiteInfoClosure_iii_cfl`：CFL 性と `ĥ=(h∘φ)×e_φ` による substitutability（既存の RS 定理を再利用）。

**`thm:main`(v)** — `V135LinearEnvelopeArith.lean`、`V135MainTheoremItemV.lean`（CI #1022）
- `thm_main_item_v`：任意の線形有限 CFG について（reduced・非空の仮定なし）、集合駆動の特性標本が `‖K‖ ≤ c·(|G|+1)^12` を満たす。`|G|` は encodingScale `|N|+|P|+Σ|rhs|`、`c` は `|M|` と `|Σ|` のみに依存。v116 演算子版も証明。

**`cor:ilt` の v116 文法出力版** — `V135CorIltV116.lean`（CI #1022）
- `cor_ilt_v116`：v116 構成器が書いた文法コードを出力する学習器。出力文法が**構文的に安定**し、その言語が目標に一致し、各出力の構成は `1400(‖K_n‖+1)^4` 歩以内。

## C. 修復した CI 失敗（すべて annotation で原因を確認）

- #1012（`c367cb9`）：bridge で `rfl` が名前付き引数より先に展開され型不一致 → `4e6caf1`
- #1014（`4e6caf1`）：同種の unit 規則 → `b7e8c45` → **#1016 GREEN**
- #1018（`20b8c5c`）：`rcases … rfl` 後の仮定名の衝突 → `09d8e43`
- #1020（`09d8e43`）：`insSym` 補助補題の simp 形、`show` の型未確定 → `64cc480` → **#1022 GREEN**
- #1024（`a27fa38`）：新しい主要定理（(iii)・(v)・cor:ilt v116・(ii)）の公理 guard を追加 → **GREEN**（依存は標準3公理のみ）

## D. 残る課題（未証明のもの）

1. **`prop:thick-ssbnf-normal` の「多項式時間で変換」**：正規化の言語保存・サイズ・厚さは既存の定理で証明済み。歩数付きの実行可能な正規化器は未実装。
2. **`thm:poly-build` の付随事項**：出力の重複除去は行っていない。標本を列として保持するコスト（`Finset.toList`）と学習器の所属判定は、v116 表現としては未課金で、既存 v79 の materialized 会計に依存。
3. 計算量は RAM／ポインタ機械の操作数であり、Lean コンパイル後の実機時間やビット計算量ではない。モノイド演算の単位コストは `M` 固定・有限が前提。

## E. 次回の最初の作業

1. HEAD の CI を確認する（失敗していれば annotations API で原因を確認）。
2. D-1：既存の `indexed_proposition74_full_package` の構成段階（terminal isolation → 二分化 → ε 除去 → unit 除去 → trim）ごとに歩数付きの実装を作り、既存の言語定理と接続する。
3. 原稿側：`thm:poly-build` の証明文は四次の評価として正しい。バケット分割や正準 ID は四次には不要、という注記は任意（原稿の変更は不要）。

## F. 変更・追加したファイル（本セッション）

- 新規 Lean：`V135CostedPrimitives.lean`、`V135PolyBuildAlgorithm.lean`、`V135PolyBuildBridge.lean`、`V135InverseHomTransducer.lean`、`V135InverseHomCFL.lean`、`V135InverseHomFinite.lean`、`V135LinearEnvelopeArith.lean`、`V135MainTheoremItemV.lean`、`V135CorIltV116.lean`
- 修正：`All.lean`（import 追加）、`V135AxiomAudit.lean`（guard 追加）
- 文書：本書・`START_HERE`・`DELTA` の冒頭、`V135_NUMBERED_CLAIMS_CROSSWALK_2026-10-10.md`（#2・#4・#11・#12 を F に）、新規 `V135_POLY_BUILD_COMPLEXITY_AUDIT.md`

## G. 変更禁止（従来通り）

`Papers`、TCS 投稿版、形式化 `main`、v88、PR #8 の merge・Ready 化、force push。

---

# 【最優先・再開用】TCS #1 Lean 形式化 引継ぎ — 2026-10-10 午後更新（Claude セッション）

> **この節が最新。** 下の「2026-10-10 (JST) 午前版」以降は履歴として残す。
> 再開手順：**この節 → GitHub の実 HEAD と最新 Actions → 実際の Lean ファイル → `Papers/01_fixed-h-cfg/main.tex`(v135)**。文書内の CI 記載より GitHub の実体を優先すること。

## A. 状態の要約（数値はすべて GitHub Actions の実結果）

| 項目 | 値 |
|---|---|
| 作業ブランチ / PR | `audit/tcs1-v128-exact-delta` / Draft PR #8（未 merge、Draft のまま） |
| **最後に GREEN を確認したコード SHA** | **`d130c3d10c111a67030aa4aa96ff919a343eb1b7`** — CI [#1008](https://github.com/growupkuriyama-hub/tcs1-lean-formalization/actions/runs/38016749202) SUCCESS（push、全5ゲート） |
| それ以前の GREEN（本セッション） | `6515d63` CI [#1004](https://github.com/growupkuriyama-hub/tcs1-lean-formalization/actions/runs/38015129745)；`51e895d` CI [#1000](https://github.com/growupkuriyama-hub/tcs1-lean-formalization/actions/runs/38013389121) / [#1001](https://github.com/growupkuriyama-hub/tcs1-lean-formalization/actions/runs/38013392163) |
| セッション開始時の最後の GREEN | `481c76d` CI #976/#977 |
| 現在の HEAD | 本文書をコミットした SHA（`git log -1`）。文書コミットの CI 結果は PR #8 で確認 |
| 原稿 | v135、sha256 `e8590799dbb889f6a375f61c6b9f8c00f3c23d6691d73561808d0989e450ecad`（Papers `2e67f3a`） |

各 GREEN run は 5 ゲートすべて成功：v128 delta 先行ビルド、theorem-facing critical path、`LeanCfgProject.TCS1.All`、`sorry` 禁止、独自 `axiom` 禁止。

## B. 本セッションで修復した CI 失敗（原因はすべてログで確認済み）

1. **CI ログが読めない問題**：このクラウド環境からは Actions のログ blob（`*.blob.core.windows.net`）が遮断される。→ ワークフローに **診断専用ステップ**を追加（`fb195d9`）：各 `lake build` 出力を `tee`（`pipefail` 付きで終了コードは不変）し、失敗時のみ `.github/scripts/lean_errors_to_annotations.py` が `error: file:line:col` を **check-run annotation** として再出力。取得は `gh api repos/<owner>/<repo>/check-runs/<job_id>/annotations`。ゲートは一切弱めていない。
2. CI #992/#993（`74654c6`）・#994（`fb195d9`）：最初の Lean エラーは **`MixedDerivationLeastClosedBridge.lean:30` termination 推論失敗**（相互再帰 theorem）。`GeneralCFGDerivationBridge.lean`（`7ff0602` の修正）は **エラーなし＝修正は有効**と確認。→ `74deed2` で `MixedDerives.rec` / `MixedSymbolsDerive.rec`（motive_1/motive_2 明示）による証明に置換。命題は不変。
3. CI #996（`2da1459`）：新規ファイルの `simpa` 1 箇所 → `0cc1b1b` で修正。
4. CI #998（`0cc1b1b`）：Lean は全成功、`axiom` grep が **コメント行頭の単語 "axiom"** に誤反応 → `51e895d` で文言のみ変更（ゲートは不変）→ **#1000 GREEN**。
5. CI #1002（`707e927`）：`Fintype` を `∧` に入れた型エラー 1 件 → `6515d63` で `Nonempty (Fintype _)` に → **#1004 GREEN**。
6. CI #1006（`471a657`）：新ファイルの import 漏れ（`reconstructionSampleWord_encoding_le_norm`）→ `d130c3d` で import 追加 → **#1008 GREEN**。

## C. 新しく Lean で証明した主要定理（CI 付き）

**`cor:li-thickness`（原稿完全形）** — `V135LiThicknessExactCorollary.lean`（CI #1000）
- `cor_liThickness_exact (H) (hlocal : PositiveImageSandwichTrivial H) : ∃ c d, c = corLiThicknessConst H ∧ d = 12 ∧ ∀ {N P} [Fintype N] [Fintype P] [DecidableEq N] (G : IndexedMixedCFG N α P) (S), IndexedMixedReduced G S → FixedHSubstitutable H L → L.Nonempty ∧ ∃ K, IsSetDrivenCharacteristicSample (BatchLanguage H) L K ∧ ‖K‖ ≤ c·(|G|+τ_G+1)^d`（`L` = 構文木言語 `MixedNonterminalLanguage G.toMixedRules S`）。
- `c` は `H`（`|M|`、窓 `n=|h(Σ⁺)|+1`）と `|Σ|` のみに依存し、文法の量化の **前** に固定。
- `|G|` = 通常の記号数 `Σ_p(1+|rhs p|)`（`IndexedMixedCFG.symbolCount`）、`τ_G` = **厳密な max–min**（`IndexedMixedCFG.ordinaryThickness`、到達性と最小性を証明）。
- characteristic sample は論文 §2 の定義そのもの（`C ⊆ L` かつ全 `C⊆K⊆L` で再構成が `L`）。再構成の型付けは **元の `H`**。
- 補題：`leastClosedLanguage_eq_mixedNonterminalLanguage`、`normalizationScale_le_symbolCount`（reduced なら `|N|+|Σ|+|P|+Σ|rhs| ≤ |Σ|+2|G|+1`）、`liThicknessEnvelope_le_poly`。
- `V135AxiomAudit.lean`：`#guard_msgs` + `#print axioms` で主要4定理の依存公理が `[propext, Classical.choice, Quot.sound]` のみであることを **ビルド時に強制**。

**`thm:main`(iv)** — `V135MainTheoremItemIV.lean`（CI #1000）、`V135ItemIVv116Operator.lean`（CI #1004）
- `thm_main_item_iv`：上記に加え、同じ `B_h` を仮説解釈に用いる **既存の materialized conservative learner** が全正例提示で Gold 安定化（`indexedFixedH_learning_materialized_core` を再利用）。
- `thm_main_item_iv_fixedWindow`：全 `h_{k,ℓ}` について（`fixedWindow_positiveImageTrivial` 経由）。
- `cor_liThickness_bound_v116`：原稿の v116 表形式 `B_h`（`v116TabulatedBatchLanguage`）に対しても同じ特性標本（演算子の外延的同一性 `v116TabulatedBatchLanguage_eq_batchLanguage_fun`）。

**`prop:finite-info-closure` (ii) の CFL 側** — `V135RegularFilterCFL.lean`（CI #1004）
- 任意の述語 CFG の typed refinement：`(A,m) ⇒* w ↔ A ⇒* w ∧ g(w)=m`（相互再帰子による両方向）。
- 新開始記号の和、有限 indexed 表示 `regularFilterGrammar`（生成規則 index `(Σ p, Fin |rhs p| → M_g) ⊕ F`）。
- `regularFilterGrammar_language`：言語 = `L(G,S) ∩ g⁻¹(F)`。`finiteInfoClosure_ii_cfl`：有限 CFG による生成 ＋ `(h×g)`-substitutable。

**v134 で追加された序論の例 `L={a,aa}`** — `V134IntroParityExample.lean`（CI #1004）：`S→a|aa` が生成、自明型付けで非 substitutable、パリティ型付けで substitutable かつ `a`,`aa` を分離。

**`thm:poly-build` の出力部分（時間定理ではない）** — `V135SubstringLiteralOutputSize.lean`（CI #1008）
- 実際の v116 規則表（B/U/L/S/ε）全体の **リテラル出力長** ≤ `(2|Σ|+7)(n_K+1)^4`、候補走査＋書き出しの合計 ≤ `(2|Σ|+11)(n_K+1)^4`。

**`prop:li-window` の class-union 節** — `V135LiWindowClassUnion.lean`（CI #1008）
- `prop_liWindow_classUnion : InKL L ↔ InLocallyTrivialRSUnion L`、`prop_liWindow_classUnion_cfl`（有限 indexed CFG による CFL と交差）。

## D. 原稿との照合結果

- v128→v135：**番号付き 30 主張＋定義 2 の本文と全 30 証明が文字列として同一**（空白正規化後、機械比較）。差分は序論・先行研究、`L={a,aa}` 例、`L₀` の位置、1 語の言い換え、文献のみ。詳細：`V135_NUMBERED_CLAIMS_CROSSWALK_2026-10-10.md`。
- `cor:li-thickness` の10項目監査：`V135_LI_THICKNESS_MAIN_IV_EXACT_AUDIT_2026-10-10.md`。

## E. まだ残る課題（未証明・未接続を明示）

1. **`thm:poly-build` の時間上界**：v116 構成器そのものの多項式時間（さらに `O(n_K^4)`）は未証明。証明済みは候補数（三次）と出力長（四次）のみ。次の具体案（すべて `O(n_K^4)` に収まる RAM 型 単位コスト・表アクセス模型）：
   (a) 因子等価表 `E[(s,i),(s',i'),ℓ]` を `ℓ` について漸化（`O(n_K^3)` 項目）；(b) 各因子スロットの正準 ID = 等しい最初のスロット（`O(n_K^4)` 参照）；(c) 前後文脈 ID も接頭辞/接尾辞等価表で同様；(d) `h` 型は 1 記号ずつ延長して `O(n_K^2)`；(e) (B) は正準親スロットからのみ出力すれば重複なし（`O(n_K^3)`）；(f) (U) は `n_K^2×n_K^2` 真偽行列に組ペア走査（`O(n_K^4)`）で書き込み、最後に走査出力；(g) 出力表＝既証明の実表（`v116EffectiveBinaryWordTable_eq_actual`、`v116UnaryRuleTable_iff` 等）との一致を証明し、コストを `V135SubstringLiteralOutputSize` と合成。
2. **`prop:finite-info-closure` (iii) の CFL 側**（CFL の（消去的）逆準同型像閉包）：外部の古典定理のまま。RS 側は証明済み。
3. **`prop:thick-ssbnf-normal` の「多項式時間で変換」**：構成とサイズ/厚さの多項式評価は証明済みだが、変換の計算時間は Lean 定理ではない（`cor:li-thickness` には不要）。
4. `cor:ilt`：v116 文法を逐次出力する学習器としての包装は未（言語としては外延的に同一）。
5. `thm:main`(v) の量化形の再監査（本セッションでは未実施）。

## F. 変更したファイル（本セッション）

- 新規 Lean：`V135LiThicknessExactCorollary.lean`、`V135MainTheoremItemIV.lean`、`V135AxiomAudit.lean`、`V135ItemIVv116Operator.lean`、`V135RegularFilterCFL.lean`、`V134IntroParityExample.lean`、`V135SubstringLiteralOutputSize.lean`、`V135LiWindowClassUnion.lean`
- 修正 Lean：`MixedDerivationLeastClosedBridge.lean`（証明のみ）、`All.lean`（import 追加）
- CI：`.github/workflows/tcs1-ci.yml`（tee＋失敗時アノテーション、ゲート不変）、`.github/scripts/lean_errors_to_annotations.py`
- 文書：本書、`START_HERE_TCS1_V128.md`・`FORMALIZATION_TCS1_V128_DELTA.md` の冒頭、`V135_LI_THICKNESS_MAIN_IV_EXACT_AUDIT_2026-10-10.md`、`V135_NUMBERED_CLAIMS_CROSSWALK_2026-10-10.md`

## G. 変更禁止（従来通り）

`Papers` の原稿・`main`、TCS 投稿版、形式化リポジトリ `main`、v88 リリース/タグ、Draft PR #8 の merge・Ready 化、force push。

## H. 次回最初の作業

1. PR #8 で HEAD の CI を確認（失敗なら annotations API で最初の Lean エラーを取得）。
2. E-1 の `O(n_K^4)` 構成器を新ファイルで実装（まず (a)(b)(e) と出力表一致、次に (U)）。
3. E-2 を最小限の補題（CFL の逆準同型像）として形式化するか、外部依存として原稿の引用範囲に明記。

---
> **以下は 2026-10-10 午前版（履歴）。** 「最新の CI #986/#987 in_progress」等は当時の記述であり、その後 #986/#987 は cancelled、最初の実エラーは上記 B-2 の通り。

# 【最優先・新ChatGPT再開用】TCS #1 Lean形式化 引継ぎ — 2026-10-10 (JST)

> **This is a durable restart packet, not a declaration of proof completion.**
> 新しい ChatGPT は **この文書 → `START_HERE_TCS1_V128.md` → GitHub Actions の最新 CI → 実際の Lean ファイル → 現行 `Papers/01_fixed-h-cfg/main.tex`** の順に確認すること。会話の印象、過去の CI 数字、文書内の古い「latest」を優先しない。
> **最重要：最後に成功を確認したコード SHA と、まだ検証されていない作業 HEAD は別物。**

## 0. 作業の正本・保護方針

- 形式化リポジトリ：`growupkuriyama-hub/tcs1-lean-formalization`
- **作業ブランチ**：`audit/tcs1-v128-exact-delta`
- **Draft PR #8**：https://github.com/growupkuriyama-hub/tcs1-lean-formalization/pull/8 （未マージのまま保持）
- **再開 Issue #9**：https://github.com/growupkuriyama-hub/tcs1-lean-formalization/issues/9
- 原稿の数学的正本：`growupkuriyama-hub/Papers/01_fixed-h-cfg/main.tex` と `PAPER.yaml` の `main`。**2026-10-10 時点内部 v135 / TCS major revision**。旧監査ファイル名の `V128` はこの形式化ブランチの歴史的名称であり、v135 の原稿と完全一致したことを意味しない。
- ユーザーの許可なく `Papers/main`、投稿済み exact snapshot、形式化リポジトリの `main`、検証済み v88 歴史的リリースを更新しない。**Draft PR #8 を勝手に merge しない。**
- **`sorry` または独自 `axiom` を証明に追加して見かけ上 CI を通さない。** 誤魔化さず未完了とする。

## 1. 本当に検証済みの最後のコミット

**最後の GREEN コード SHA**：`481c76d50085e69fa1af4c2e68cd7ef6644fc839`。

- CI **#976**：https://github.com/growupkuriyama-hub/tcs1-lean-formalization/actions/runs/38000986304 — **success**
- CI **#977**：https://github.com/growupkuriyama-hub/tcs1-lean-formalization/actions/runs/38000989260 — **success**
- 検証範囲：v128 finite-rule delta の先行ビルド、theorem-facing critical path、`LeanCfgProject.TCS1.All`、no-`sorry`、no-project-`axiom` の workflow checks。
- それ以前の主要 GREEN：#954（SHA `0839dca9b0f3279ab7954bee90f0bdd8b663c859`）、#966/#967（SHA `4ae2f709cd2107fafd2173586fa43d073877e438`）、#968/#969（SHA `5865f1b5561e9fcd4ebe4073ce30edd63cbdcd01`）。これらは証明の発展過程であり、最終 GREEN は上記 #977。

GREEN までの数学的実装（`LeanCfgProject/TCS1/` 配下）：

1. **`V128PositiveWindowKernelForward.lean` / `V128PositiveWindowKernelConverse.lean`**：正語像 `h(Σ⁺)` の局所自明性と正語に限定した固定窓 kernel refinement の両方向、明示窓幅 `n=|h(Σ⁺)|+1`、fixed-window substitutability への転送。原稿 `prop:li-window` の重要な数学的中核。ただし class union characterization などの全ての文章上の節まで exact-version 照合した保証ではない。
2. **`V128LocallyTrivialThickness.lean`**：固定窓の証人長・SSBNF 特性標本パッケージ。もともとは `hshort`・規則数・正規化評価等の仮定を要求する条件付き定理。
3. **`V128IndexedNormalizationCertificate.lean`**：有限 indexed CFG から SSBNF の状態数と非開始記号の短い成功導出語を構成。`|w_X|≤1+n_G²(τ_R+1)`。
4. **`V128IndexedLocallyTrivialCharacteristicData.lean`**：`indexedLocallyTrivialCharacteristicData_package` と `indexedLocallyTrivialCharacteristicData_nonempty_package`。元のモノイド型付け **`H` 自身**の characteristic batch reconstruction `BatchLanguage H K = L(G)` を確保し、源の `YieldBound` と indexed `normalizationScale` で明示多項式 envelope に抑える。**非空対象のうち `{ε}` も場合分けで含む**。ここまでは #977 で GREEN。
5. 以前からの資産：`IndexedNormalizationLanguage.lean`（源言語と normalized SSBNF の言語保存）、`IndexedSection7Bridge.lean`、`IndexedFixedHBridge.lean`、`IndexedNormalizationCounts.lean`（状態/terminal/binary rule の size bounds）。**既存を再実装しない。**

※ この GREEN は **原稿 `cor:li-thickness` と `thm:main`(iv) の universal arbitrary-reduced-CFG 文言まで完全証明したという意味ではない**。

## 2. GREEN 以後の追加作業：再検証が必要

GREEN `481c76d` からの作業順：

- `f1b3da5bc5be2023a0566b04f5168d1965eb1359`：新規 `MixedDerivationLeastClosedBridge.lean`。成功した parse tree `MixedDerives` の語は `LeastClosedLanguage` に属すことを任意の閉な解釈に対して証明する予定の bridge を追加。
- `b7bed480b27ab6ec00579f561acf5780c20b14ff`：`indexedMixedThicknessAtMost_implies_yieldBound` と、それを使う `indexedLocallyTrivialCharacteristicData_of_ordinaryThickness`。
- `0bdceca01e3c6e4820e28774b67544a4dd4da07f`：`TCS1.All` に新 bridge を追加。
- `674e97ec1390a302689b00380ca7c55ed8b32ae7`：`indexedLocallyTrivialCharacteristicData_reduced_source` を追加。reducedness から start 語が存在すること、start の存在から `normalizationScale>0` を得る構成。
- `7ff060276308b5fce33f55ce213afe4b79b5ff11`：後述 CI failure の最初のエラーを修正するため、`GeneralCFGDerivationBridge.lean` の `decreasing_by omega` を `decreasing_by; simp_wf; simp` に変更。**この修正の成功は保存時点で未確認**。

**2026-10-10 保存時点の作業 HEAD**：`7ff060276308b5fce33f55ce213afe4b79b5ff11`。再開時にはより新しい HEAD がないか確認すること。

### 結果が確定した失敗（隠さない）

**CI #984/#985**、head `674e97e` は両方 **failure**。CI #985: https://github.com/growupkuriyama-hub/tcs1-lean-formalization/actions/runs/38003724745 。

- `Build v128 finite-rule delta first`: success
- `Build theorem-facing critical path`: success
- `Build TCS1 facade`: failure
- 最初のエラー：`LeanCfgProject/TCS1/GeneralCFGDerivationBridge.lean:50:14`、`omega could not prove the goal`。termination decreasing goal の `rhs.length` と `(Sum.inr a :: rhs).length` に対して簡約が必要。**新 bridge から以前未ビルドだった既存ファイルの import が到達可能になった際に発見された。** これをコミット `7ff0602` で対処したが後続の別エラーはまだあり得る。
- #982/#983 は後続 push で cancelled。**cancelled を success と読まない。**

**最新の CI #986/#987（7ff0602）**：
- https://github.com/growupkuriyama-hub/tcs1-lean-formalization/actions/runs/38007485794
- https://github.com/growupkuriyama-hub/tcs1-lean-formalization/actions/runs/38007490367
- 文書作成時点：**in_progress**。GitHub 上で実際の結論を先に確認すること。新 proof を「機械検証済み」と認定するのは成功後のみ。

## 3. 現行原稿で要求される exact statement

`Papers/01_fixed-h-cfg/main.tex` のラベルを読むこと：

- **`prop:li-window`**：非空アルファベット `Σ`、有限モノイド morphism `h`、`n=|h(Σ⁺)|+1`、positive image が locally trivial ↔ some positive-word window-kernel refinement、explicit `(n,n)`、窓正像の局所自明性、`KL` のクラス合併および CFL 交差版。両方向の主 kernel theorem は実装・GREEN だが全項目の原稿一致は別監査。
- **`cor:li-thickness`**：固定 `h` で `h(Σ⁺)` locally trivial ならば、**任意の reduced CFG `G_*`** が表す **任意の非空 `L∈C_h`** には `B_h` の characteristic data があり、**encoded sample size** は `poly(|G_*|,τ_{G_*})`。空言語は別扱い。論文中の ordinary thickness は `τ_G=max_A min\{|w|:A⇒*_G w\}`（空語可）。
- **`prop:thick-ssbnf-normal`**：源 reduced CFG `G_*` から equivalent **reduced separated-start SSBNF** grammar `G` への polynomial-time conversion、`|G|≤q_size(|G_*|)`, `τ_G≤q_thick(|G_*|,τ_{G_*}+1)`。
- **`thm:main`(iv)**：上記 `cor:li-thickness` と同じ universal form を統合学習定理の一部として要求。
- 文書内の v128 主張30件は **歴史的 crosswalk**。現行 v135 を最新の対象として再抽出すること。旧 `24R/3B/1P/2O` 件数は証明後に更新されていないため **進捗率に使わない**。

実際の符号化：`IndexedMixedCFG.normalizationScale = |N|+|Σ|+|P|+∑_p |rhs(p)|`。これは具体的多項式 envelope のパラメータ。`|G_*|` の exact な表現と count/coding convention、普通の thickness の対応を照合する必要がある。上記 `MixedDerivationLeastClosedBridge` は通常の parse-tree thickness ⇒ 構成で使う `YieldBound` に橋を架ける目的。

## 4. 次の ChatGPT が取るべき順番

1. GitHub `audit/tcs1-v128-exact-delta` HEAD を取得、**#986/#987 またはもっと新しい最新 CI** の結論・失敗ログを取得。**この文書を読むだけで終えない。**
2. 未成功なら CI エラーを一件ずつ修正。第一修正 `7ff0602` の `GeneralCFGDerivationBridge` termination から検証。新 `MixedDerivationLeastClosedBridge` の相互再帰の termination/typing、reduced-source theorem の `Fintype.card_pos` も検査。差分修正は Draft PR ブランチだけに push。green を得るまで検証済みと宣言しない。
3. green 後、最新コミット SHA と CI URL をここに追記（旧記録は消さず日時をつける）、`START_HERE_TCS1_V128.md` と `FORMALIZATION_TCS1_V128_DELTA.md` の冒頭、Issue #9、PR #8 に成功の条件と scope を反映。
4. 本文 v135 とコードの `cor:li-thickness`、`thm:main`(iv) の型・仮定・`B_h` sample characteristic property・encoded norm（`∑_{w∈K} (|w|+1)`）・源 CFG size と ordinary `τ_G` の対応を一つずつ照合。`BatchLanguage H K = L` と「all data extensions retain target」という学習定理側の characteristic-data 定義の関係も確認。
5. 形式化全体では、(a) `thm:main` の precise packaging、(b) finite-information CFL closure、(c) v116 の **実際の生成アルゴリズム** `O(n_K^4)` operation-cost bridge、(d) 現行版の numbered claim audit が残る。**finite tables/word-rule counts と machine-time bound を混同しない。**

## 5. 詳細ファイルと既存資産（再実装禁止）

- `START_HERE_TCS1_V128.md` — 歴代 CI と再開指示
- `FORMALIZATION_TCS1_V128_DELTA.md` — 数十件の claim/proof 差分台帳
- `V128_LI_THICKNESS_EXACT_SCOPE_AUDIT_2026-10-09.md` — `cor:li-thickness` の最初の exact gap 監査（これ以降に部分 bridge を追加済み）
- `V128_NUMBERED_CLAIMS_ONE_TO_ONE_AUDIT_2026-10-09.md` / `V128ThirtyClaimCrosswalk.lean` — v128 時点の30件照合。**`#check` は原稿完全証明を意味しない。**
- `IndexedNormalizationFacade.lean`, `IndexedConcreteSSBNFNormalization.lean`, `IndexedNormalizationLanguage.lean`, `IndexedNormalizationCounts.lean`, `IndexedSection7Bridge.lean`, `IndexedFixedHBridge.lean` — 元の言語/正規化/サイズ/characteristic data に再利用する正本。
- `V128SubstringEffectiveBinaryTable.lean` 等 — 以前の verified finite production tables、実行可能な B table、v116 三切り区間上界。executable whole-rule writer の full `O(n_K^4)` はまだ未了。

## 6. そのまま新しい ChatGPT に渡せる開始プロンプト

> `growupkuriyama-hub/tcs1-lean-formalization` の TCS #1 Lean 形式化を前スレッドから引き継ぎます。最初に作業ブランチ `audit/tcs1-v128-exact-delta` の `NEXT_CHAT_HANDOFF_TCS1_2026-10-10.md` と `START_HERE_TCS1_V128.md`、Issue #9、Draft PR #8 を GitHub connector で読み、最新 HEAD と CI の実際の結果を確認してください。最後の確認済み green は `481c76d`、CI #976/#977。新 bridge と reduced source theorem は `7ff0602` まで実装済みですが、CI #984/#985 の `GeneralCFGDerivationBridge.lean:50` エラーを修正した直後で、新 SHA の CI は未確認です。まず CI ログに従って false success を避けて green に戻してください。その後 `Papers/01_fixed-h-cfg/main.tex` 現行 v135 と `cor:li-thickness`、`thm:main`(iv) を精密に照合してください。既存形式化を再実装しない。PR は Draft のまま、原稿・main・v88 は勝手に変更しない。

## 7. 記憶と権威順位

永続的に再現可能な正本は **GitHub のファイル、コミット、CI と原稿の実体**。ChatGPT の過去会話や自動的に抽出される Memory は、完全な Lean ログ/コード/ハッシュを保証しない。本ファイルを新しいチャットに明示し、GitHub connector のソースとその時点の CI を読むこと。過去の誤った「成功」印象をコピーしない。
