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
