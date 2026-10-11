# peg-hs

PEG（Parsing Expression Grammar）の定義から Haskell のパーサーを生成するツールチェーン。

[English README](README.md)

- 標準 PEG の全構文と、直接と間接の左再帰を受理する（bounded left recursion, Medeiros et al. 2014）
- happy / alex 方式のスタンドアロン生成器。`.peg` から決定的に `.hs` を生成する（同一入力からバイト単位で同一の出力）
- 各規則が結果型とセマンティックアクションを持ち、生成されたパーサーは利用者の AST を直接返す

**ステータス：設計フェーズ。** 仕様書と ADR は完成しており、実装は未着手。

仕様は [docs/specifications.md](docs/specifications.md)、設計決定は [docs/adr/](docs/adr/) を参照。

## 開発

ツールチェーンは ghcup が recommended とする版を使う（GHC 9.10.3、cabal-install 3.16.1.0、HLS 2.14.0.0）。
コンパイラの版は `cabal.project` で固定する。
[mise](https://mise.jdx.dev/) を使う場合は、同梱の `mise.toml` が ghcup のバイナリをプロジェクトの PATH に加える。

```sh
ghcup install ghc 9.10.3
ghcup install cabal 3.16.1.0
```

クローン後、git の hook を有効化する。
コミット済みの ADR は変更不可であり、[adr-guard](https://github.com/tett23/adr-guard) が pre-commit hook と CI で変更を拒否する。

```sh
git config core.hooksPath .githooks
```

性能の退行は手元のベンチマークで検出する。
peg-runtime や peg-codegen に触れる変更では、変更前後で同一マシンのベンチマークを比較すること（ADR 0007）。

## ライセンス

[MIT](LICENSE)
