# ADR 0048: Hackage へのアップロードのコマンドと、peg-cli の Haddock の tarball を正す

ステータス: 採択

## 文脈

[ADR 0044](0044-release-v0-1-0.md) を実装したところ、ADR の記述に二つの誤りが見つかった。

一つめは、Hackage へのアップロードのコマンドである。
[ADR 0044](0044-release-v0-1-0.md) は「候補（`--candidate`）として上げる」と書いた。
しかし cabal-install 3.16 の `cabal upload` に `--candidate` はない。
`cabal upload` は既定で候補として上げ、`--publish` を付けたときだけ公開する。
ADR のとおりのコマンドは、オプションの誤りで失敗する。

二つめは、Haddock の tarball の数である。
[ADR 0044](0044-release-v0-1-0.md) のテスト設計は、Release に「五つの Haddock の tarball」が添付されることを求めた。
実装した `release.yml` は、ライブラリを持つ四つのパッケージ（peg-runtime、peg-grammar、peg-codegen、peg-lsp）の tarball だけを作った。
peg-cli は実行ファイルだけのパッケージで、ライブラリがないためである。
正しいのは五つである。
peg-cli も Hackage のパッケージであり、その文書のページがないと、五つのパッケージのうち一つだけ文書が欠ける。
`cabal haddock --haddock-for-hackage --haddock-executables` は、実行ファイルだけのパッケージからも Hackage に上げられる tarball を作る。

## 実装すること

### アップロードのコマンド

- 候補として上げるコマンドは `cabal upload FILE...` と `cabal upload --documentation FILE...` とする
- 公開するコマンドは `cabal upload --publish FILE...` と `cabal upload --publish --documentation FILE...` とする
- プレリリースのタグでは候補として上げるだけにし、`--publish` を使わない。[ADR 0044](0044-release-v0-1-0.md) の方針は変えない
- CONTRIBUTING（日本語と英語）のリリースの手順を、このコマンドで書く

### peg-cli の Haddock の tarball

- `release.yml` で、peg-cli の Haddock の tarball を `cabal haddock --haddock-for-hackage --haddock-executables peg-cli` で作る
- Release に添付する Haddock の tarball が五つであることを、ワークフローで検査する
- Haddock の網羅の検査（`scripts/haddock-coverage.sh`）は、これまでどおり四つのライブラリの公開モジュールに限る。peg-cli の実行ファイルのモジュールは公開の API ではないためである
- CONTRIBUTING の手順の Haddock の tarball の一覧に、peg-cli を加える

## 実装しないこと

- peg-cli にライブラリを加えること。実行ファイルの内部のモジュールを公開の API にすることになり、PVP の対象が増える
- peg-cli の実行ファイルのモジュールの Haddock の網羅の検査

## テスト設計

自動テストは書けないので、次のように確かめる。

- 手元で `cabal haddock --haddock-for-hackage --haddock-executables peg-cli` が `peg-cli-0.1.0.0-docs.tar.gz` を作ることを確かめる
- `v0.1.0-rc1` の Release に、五つの sdist と五つの Haddock の tarball が添付されることを確かめる。数が五つでなければ、ワークフローが失敗する
- `cabal upload --help` に `--publish` があり、`--candidate` がないことを確かめる

## トレードオフ

- peg-cli の文書のページは、実行ファイルのモジュールの一覧になる。利用者が読むのは README と `peg-hs help` なので、ページの中身は薄い。それでも、五つのパッケージで文書の有無がそろう
- 実行ファイルの Haddock の生成のぶん、リリースのワークフローが少し長くなる
