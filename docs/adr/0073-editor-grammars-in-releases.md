# ADR 0073: エディタの文法をリリースの配布物に含める

ステータス: 採択（未実装）

## 文脈

`.hpeg` のシンタックスハイライトには、TextMate の文法と tree-sitter の文法の二つがある（[ADR 0034](0034-syntax-highlighting.md)、[ADR 0069](0069-richer-highlighting-and-format-on-save.md)）。
TextMate の文法は `editors/textmate/hpeg.tmLanguage.json` に、tree-sitter の文法は `editors/tree-sitter-hpeg/` に置いている。
tree-sitter の文法には、生成したパーサー（`src/parser.c`）、外部スキャナー（`src/scanner.c`）、問い合わせ（`queries/` の `highlights.scm`、`injections.scm`、`folds.scm`、`indents.scm`、`locals.scm`）がある。

ところが、どちらもリリースの配布物には入っていない。
GitHub の Releases に置くのは、五つのパッケージのソースの tarball と文書、Linux と macOS の実行ファイルの tar.gz、`SHA256SUMS` である（`.github/workflows/release.yml`）。
仕様書は「エディタの文法と VS Code の拡張機能は、リポジトリの `editors/` で配布する」としており、利用者はリポジトリを clone しないと文法を手に入れられない。
実行ファイルを Releases から入れた利用者は、言語サーバー、lint、整形は使えるのに、ハイライトだけは別の手段で手に入れることになる。

リポジトリの持ち主は、TextMate の形式と tree-sitter の形式の文法を、配布物に含めると決めた。

## 実装すること

### 文法のアーカイブ

- リリースに、エディタの文法のアーカイブ `peg-hs-editors-<版>.tar.gz` を加える。`<版>` はタグから `v` を除いたもので、実行ファイルのアーカイブと同じ付け方である
- アーカイブの中身は次のとおりとする。最上位のディレクトリは `peg-hs-editors-<版>/` とする

  ```
  peg-hs-editors-<版>/
    LICENSE
    README.md            -- エディタごとの入れ方（下の節）
    textmate/
      hpeg.tmLanguage.json
    tree-sitter-hpeg/
      grammar.js
      package.json
      tree-sitter.json
      queries/           -- 問い合わせのすべて
      src/               -- parser.c、scanner.c、grammar.json、node-types.json、tree_sitter/
  ```

- tree-sitter の文法は、生成済みの `src/` を含める。利用者のエディタ（Neovim、Helix）は `src/` から C でパーサーを作るので、tree-sitter の CLI と Node.js がなくても入れられる
- アーカイブはプラットフォームによらないので、一つだけ作る

### 実行ファイルのアーカイブ

- 実行ファイルのアーカイブ（`peg-hs-<版>-<プラットフォーム>.tar.gz`）にも、上と同じ `textmate/` と `tree-sitter-hpeg/` を `editors/` の下に入れる。Releases から実行ファイルを入れた利用者が、同じアーカイブでハイライトもそろえられるようにするためである

### 作り方

- アーカイブの中身を作るシェルスクリプト `scripts/pack-editors.sh` を置く。引数で出力先のディレクトリを受け取り、上の構成のファイルを `editors/` から写す。写すファイルは、スクリプトの中に列挙する（ディレクトリをまるごと写さず、`node_modules` やビルドした `parser.so` が入らないようにする）
- `release.yml` は、このスクリプトで文法のアーカイブを作り、実行ファイルのアーカイブにも同じスクリプトで `editors/` を加える
- アーカイブの `README.md` は、`editors/README.md` として置く。中身は、TextMate の文法を使うエディタ（VS Code の手動の設定、Sublime Text など）と、tree-sitter の文法を使うエディタ（Neovim、Helix）への入れ方の要点と、リポジトリの README のエディタの節への案内とする

### 文書

- docs/specifications.md の配布と版の節を、エディタの文法を Releases のアーカイブでも配布すると改める
- README のインストールとエディタの節に、Releases の文法のアーカイブと、実行ファイルのアーカイブの `editors/` を書く。Neovim と Helix の設定例は、clone したリポジトリの代わりに、展開したアーカイブの場所でも使えることを書く

## 実装しないこと

- VS Code の拡張機能の vsix の作成と Marketplace への公開（[ADR 0044](0044-release-v0-1-0.md) の残課題のまま）
- tree-sitter のパーサーをビルドした共有ライブラリ（`.so`、`.dylib`）の配布。プラットフォームごとに要り、エディタが `src/` から作れる
- tree-sitter の文法の npm や crates.io への公開
- Hackage のパッケージ（peg-cli など）への文法の同梱

## テスト設計

先に書き、いまの実装で失敗させる。

- **中身の一覧**：CI の `editors` のジョブで `scripts/pack-editors.sh` を一時ディレクトリに対して動かし、出てきたファイルの一覧が、期待する一覧（テストのファイルに書く）と一致すること。`node_modules`、`parser.so`、テストのファイルが入らないこと
- **写したものが元と同じこと**：写した各ファイルが、`editors/` の元のファイルと同じ内容であること
- **写した tree-sitter の文法が使えること**：写した `tree-sitter-hpeg/` で、tree-sitter の CLI がパーサーを作り、リポジトリのすべての `.hpeg` を `ERROR` なく読めること
- **リリース**：自動テストにはしない。次の `v` のタグのリリースで、Releases に `peg-hs-editors-<版>.tar.gz` があり、実行ファイルのアーカイブに `editors/` があることを確かめる。`SHA256SUMS` に文法のアーカイブが含まれることも確かめる

## トレードオフ

- 同じ文法を、文法のアーカイブと二つの実行ファイルのアーカイブの、三つに入れる。文法は合わせて数百 KB で、実行ファイルに比べて小さい
- 写すファイルをスクリプトに列挙するので、問い合わせなどのファイルを足したときは、スクリプトと期待する一覧も直す必要がある。中身の一覧のテストが、直し忘れを見つける
- 生成済みの `parser.c` を配るので、利用者のエディタの tree-sitter の版によっては、パーサーの ABI が合わないことがありうる。いまも、リポジトリから入れる利用者は同じ `parser.c` を使っており、この ADR で変わらない

## 参考文献

- tree-sitter, Creating parsers（生成したパーサーと `tree-sitter.json`）. https://tree-sitter.github.io/tree-sitter/creating-parsers/
