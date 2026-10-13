# ADR 0058: プレリリースを Hackage に上げない

ステータス: 採択

## 文脈

[ADR 0044](0044-release-v0-1-0.md) は、プレリリースのタグ（`v0.1.0-rc1` など）でも、Hackage に候補（candidate）として上げて表示を確かめると定めた。
Hackage の版は rc を表せず、`0.1.0.0` を一度公開すると取り消せないので、rc は公開せず、候補として上げるだけにする、という決定である。
[ADR 0048](0048-release-commands-and-haddock-of-peg-cli.md) は、そのためのコマンドを `cabal upload`（候補）と `cabal upload --publish`（公開）に正した。

リポジトリの持ち主は、rc が取れるまで Hackage には何も上げないと決めた。
候補も上げない。

候補を上げる手間に比べて、rc の段階で得られるものが少ないためである。
rc は GitHub の Release で配布しており、Haddock の tarball も Release に添付している（[ADR 0044](0044-release-v0-1-0.md)）。
Hackage での表示は、正式な版を公開する前に候補として一度確かめれば足りる。
rc のたびに候補を上げると、Hackage の資格情報を使う手作業が rc の数だけ増える。

## 実装すること

- プレリリースのタグでは、Hackage に何も上げない。候補も上げない
- 正式な版（`v0.1.0` など）では、これまでどおり、まず候補として上げて表示を確かめ、その後に `--publish` を付けて公開する（[ADR 0048](0048-release-commands-and-haddock-of-peg-cli.md)）
- CONTRIBUTING（日本語と英語）のリリースの手順の Hackage の節を、上のとおりに改める
- docs/specifications.md の「プレリリースは Hackage に公開せず、候補として上げて表示を確かめるだけにする」を、「プレリリースは Hackage に上げない。正式な版を公開する前に、候補として上げて表示を確かめる」に改める
- README（日本語と英語）と CONTRIBUTING の冒頭の状態の表示を、最新のプレリリース（`v0.1.0-rc2`）に合わせる。どちらも `v0.1.0-rc1` のままになっている
- [ADR 0044](0044-release-v0-1-0.md) のステータスを「採択→プレリリースの Hackage への候補のアップロードは ADR 0058」に変える

## 実装しないこと

- 正式な版の手順の変更
- Hackage へのアップロードの自動化（[ADR 0044](0044-release-v0-1-0.md) と同じく行わない）

## テスト設計

自動テストは書けない。
実装の後に、CONTRIBUTING、docs/specifications.md、README を読み、プレリリースで Hackage に上げる手順が残っていないこと、正式な版の手順が変わっていないことを確かめる。

## トレードオフ

- Hackage での表示の問題（Haddock の崩れ、CHANGELOG の表示、依存の範囲）に気付くのが、正式な版の直前になる。Haddock の網羅と `cabal check` は CI で確かめているので、表示の問題は少ないと見込む。候補で問題が見つかれば、正式な版を打つ前に直す
- rc の利用者は、Hackage からではなく、GitHub の Release か `cabal.project` の `source-repository-package` から入れる。README の導入の節に、すでにこの方法を書いている
