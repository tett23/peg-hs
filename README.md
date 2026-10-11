# peg-hs

PEG（Parsing Expression Grammar）の定義から Haskell のパーサーを生成するツールチェーン。

- 標準 PEG の全構文と、直接・間接の左再帰をサポートする（bounded left recursion, Medeiros et al. 2014）
- happy / alex 方式のスタンドアロン生成器。`.peg` から決定的に `.hs` を生成する
- 各規則が結果型とセマンティックアクションを持ち、パーサーは利用者の AST を直接返す

仕様は [docs/specifications.md](docs/specifications.md)、設計決定は [docs/adr/](docs/adr/) を参照。

## 開発

クローン後、git の hook を有効化する。
コミット済みの ADR の変更は [adr-guard](https://github.com/tett23/adr-guard) が pre-commit hook と CI で拒否する。

```sh
git config core.hooksPath .githooks
```

性能の退行は手元のベンチマークで検出する。
peg-runtime や peg-codegen に触れる変更では、変更前後で同一マシンのベンチマークを比較すること（ADR 0007）。
