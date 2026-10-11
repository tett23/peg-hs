# peg-hs

peg-hs は PEG 定義から Haskell のパーサーを生成するツールチェーンです。

## ディレクトリ構成

- **docs/specifications.md** 製品仕様書。実装の詳細はここに書かない
- **docs/adr/** リポジトリ全体の ADR を配置する。ADR のファイル名は連番+何を実装するか。ADR には実装すること、実装しないこと、テスト設計、あればトレードオフを含める。ADR は連番の通りに /goal で自動実装される。ADR はコミット後、変更不可。変更が必要な場合は新たな ADR を作成する
- **packages/** cabal パッケージ（peg-runtime, peg-grammar, peg-codegen, peg-cli）を配置する
- **conformance/** 実在する言語の文法による適合性テスト（非公開パッケージ peg-conformance）と、取り込んだテストデータを配置する
- **docs/conformance/** 適合率のスナップショットを配置する。コミット後は変更不可

## 関連リポジトリ

- Golem（組版システム）が本ライブラリの最初の利用者だが、peg-hs は Golem に依存しない汎用ライブラリとして開発する

## skills

- 日本語の文章を書くときは cognitive-rhythm-writing japanese-tech-writing スキルを使用する。
