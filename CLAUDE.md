# peg-hs

peg-hs は PEG 定義から Haskell のパーサーを生成するツールチェーンです。

## ディレクトリ構成

- **docs/specifications.md** 製品仕様書。実装の詳細はここに書かない
- **docs/syntax.md** .hpeg 記法の利用者向け解説とサンプル。採択済みの ADR の内容だけを反映する。記法に関わる ADR のステータスを採択にしたときは、同じコミットでこの文書を更新し、冒頭の「反映している ADR」の一覧も更新する
- **docs/adr/** リポジトリ全体の ADR を配置する。ADR のファイル名は連番+何を実装するか。ADR には実装すること、実装しないこと、テスト設計、あればトレードオフを含める。ADR は連番の通りに /goal で自動実装される。ADR はコミット後、変更不可。変更が必要な場合は新たな ADR を作成する
- **packages/** cabal パッケージ（peg-runtime, peg-grammar, peg-codegen, peg-cli）を配置する
- **conformance/** 実在する言語の文法による適合性テスト（非公開パッケージ peg-conformance）と、取り込んだテストデータを配置する
- **docs/conformance/** 適合率のスナップショットを配置する。コミット後は変更不可
- **docs/benchmarks/** 計測のスナップショットを配置する。コミット後は変更不可で、adr-guard が変更を拒否する
- **scripts/** 生成物の再生成（`regen-fixtures.sh`、生成器か文法を変えたら実行する）と、文字参照の表の生成（`gen-entities.py`）

## ツールチェーン

- 既定の `cabal` は ghcup の latest に切り替わっていることがある。コマンドでは recommended の `cabal-3.16.1.0` を使う（`CABAL=cabal-3.16.1.0 scripts/regen-fixtures.sh` など）

## 言語

- Haddock（公開モジュールの API 文書）は英語で書く
- ADR、仕様書、syntax.md は日本語で書く

## 関連リポジトリ

- Golem（組版システム）が本ライブラリの最初の利用者だが、peg-hs は Golem に依存しない汎用ライブラリとして開発する

## skills

- 日本語の文章を書くときは cognitive-rhythm-writing japanese-tech-writing スキルを使用する。
