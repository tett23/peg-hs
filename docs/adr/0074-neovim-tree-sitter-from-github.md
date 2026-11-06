# ADR 0074: Neovim の tree-sitter の文法を、clone せずに GitHub から入れる例を README に足す

ステータス: 採択（未実装）

## 文脈

README の Neovim の節（「ハイライト」）は、nvim-treesitter の main ブランチに tree-sitter の文法を登録する例を載せている（[ADR 0069](0069-richer-highlighting-and-format-on-save.md)）。
例は `install_info = { path = '/path/to/peg-hs/editors/tree-sitter-hpeg', queries = 'queries' }` で、手元に peg-hs のリポジトリを clone しておく必要がある。
[ADR 0073](0073-editor-grammars-in-releases.md) の後は、リリースのアーカイブを展開した場所も `path` に書けるが、展開する手間は残る。

nvim-treesitter の main ブランチは、`path` の代わりに `url` を書くと、GitHub からリポジトリの tarball を取ってきて、パーサーを作る。
`lua/nvim-treesitter/install.lua`（2026-11-06 に確かめた e289100）では、次のように扱う。

- `url` のとき、`<url>/archive/<revision>.tar.gz` を取ってきて展開する。`revision` を書かなければ `main` を取る
- `location` は、展開したディレクトリからの、文法のディレクトリへのパスである
- `queries` は、`path` のときは `path` からのパスだが、`url` のときは展開したディレクトリ（リポジトリのルート）からのパスである。`location` からではない。そのため、`path` のときの `queries = 'queries'` と、`url` のときの `queries = 'editors/tree-sitter-hpeg/queries'` で、書き方が違う
- 更新が要るかの判定は、`revision` を書いたときは入れた版と比べる。書かないときは、問い合わせのリンク先が nvim-treesitter の同梱の問い合わせと同じかで判定する。`url` から写した問い合わせは同梱のものと別の場所にあるので、`:TSUpdate` のたびに入れ直す

### 確かめたこと

2026-11-06 に、Neovim 0.12.6 と nvim-treesitter main の e289100 で確かめた。`revision` なしの例は、リポジトリの持ち主の dotfiles の環境で、peg-hs の afd9b15 の時点で確かめた。`revision` 付きの例と haskell のパーサーは、設定を一時ディレクトリに分けた環境（`XDG_CONFIG_HOME` などを変えたもの）で確かめた。

- `url = 'https://github.com/tett23/peg-hs'`、`location = 'editors/tree-sitter-hpeg'`、`queries = 'editors/tree-sitter-hpeg/queries'` で、hpeg が GitHub から入り、`queries/hpeg/` に `highlights.scm`、`injections.scm`、`locals.scm`、`folds.scm`、`indents.scm` が写された。`revision` なし（main の先頭）と、`revision = 'v0.1.0-rc3'` の二つで入った。`revision` を書いたときは、`parser-info/hpeg.revision` に `v0.1.0-rc3` が書かれた
- `packages/peg-grammar/grammar/Peg.hpeg` で、`vim.treesitter.start` が通り、`@keyword.directive`、`@function`、`@string`、`@comment`、`@operator` などの capture が付いた
- haskell のパーサー（`:TSInstall haskell`）も入れると、`injections.scm` によって、verbatim ブロックの `import` に `haskell` の `@keyword.import` が、アクションの構築子に `haskell` の `@constructor` が付いた。haskell のパーサーがなければ、Haskell の断片には色が付かない
- `foldexpr` を `vim.treesitter.foldexpr()` にすると、折り畳みの深さが規則ごとに付いた。折り畳みの範囲が `folds.scm` の意図どおりかは、画面で確かめていない

確かめていないことは、次のとおりである。

- `indents.scm` による字下げの動き
- 実際の画面での見え方
- `revision` を書いたときに、`:TSUpdate` が入れ直さないこと（上の判定は `install.lua` を読んで書いた）

## 実装すること

### README の Neovim の節

README.md と README.ja.md の Neovim の節の「ハイライト」に、次のものを足す。

- clone せずに GitHub から入れる例。いまの `path` の例の前に置き、`path` の例は「手元の clone か、リリースのアーカイブを展開した場所から入れる例」として残す

  ```lua
  vim.api.nvim_create_autocmd('User', { pattern = 'TSUpdate', callback = function()
    require('nvim-treesitter.parsers').hpeg = { install_info = {
      url = 'https://github.com/tett23/peg-hs',
      location = 'editors/tree-sitter-hpeg',
      queries = 'editors/tree-sitter-hpeg/queries',
      revision = 'v0.1.0-rc3',
    } }
  end })
  ```

- `queries` が、`url` のときはリポジトリのルートからのパスで、`path` のときと書き方が違うこと
- `revision` にリリースのタグを書くと、その版の文法を入れること。書かなければ main の先頭を入れ、`:TSUpdate` のたびに入れ直すこと。言語サーバー（`peg-hs lsp`）と同じ版のタグを書くと、ハイライトと診断の記法の版がそろうこと
- Haskell の断片に色を付けるには、haskell のパーサーも要ること（`:TSInstall haskell`）
- 見出しの「（未確認）」は外さない。外すかどうかは、リポジトリの持ち主が実機で確かめてから決める（[ADR 0044](0044-release-v0-1-0.md)）

例の `revision` は、リリースのたびに最新のタグに直す。README の版の表記（状態の行、インストールの例、`cabal.project` の例）と同じ扱いである。

### 文書

- docs/specifications.md のエディタの支援の節の、Neovim の記述に、GitHub から入れられることを一文で加える
- docs/specifications.md の未決事項に、Helix で clone せずに git から文法を入れる例を README に足すことを加える

## 実装しないこと

- Helix の節の変更。Helix の `[[grammar]]` の `source` にも `git` と `rev` と `subpath` を書けるが、確かめていない。Helix の利用者はまだ少ないと見て、docs/specifications.md の未決事項に加えて、しばらく扱わない
- nvim-treesitter の本体への hpeg の登録の提案
- nvim-treesitter の master ブランチ（古い版）の例の変更
- 「（未確認）」の見出しを外すこと

## テスト設計

README の例なので、自動テストにはしない。
README を書いた後に、上の「確かめたこと」と同じ一時的な環境で、README に書いた例をそのまま写して、次を確かめる。

- README の例（`revision` 付き）で `:TSInstall hpeg` が通り、`queries/hpeg/` に五つの問い合わせが写され、`Peg.hpeg` に capture が付くこと
- `revision` を消した例でも入ること
- `:TSInstall haskell` の後に、verbatim ブロックとアクションに `haskell` の capture が付くこと
- `revision` を書いたとき、二度目の `:TSUpdate hpeg` が入れ直さないこと。確かめられなければ、README には「入れ直す」とだけ書き、入れ直さないとは書かない

README には、確かめたことだけを書く。

## トレードオフ

- 例の `revision` をリリースのたびに直す手間が増える。直し忘れると、古い版の文法を入れる例になる。README の版の表記と同じ時に直すので、手間は小さい
- `revision` を例に書くと、main で記法を変えた後、リリースまでの間は、新しい記法に色が付かない。main を追いたい利用者は `revision` を消せばよいことを README に書く
- 例が `url` と `path` の二つになり、節が長くなる。clone しない利用者のほうが多いと見て、`url` の例を先に置く

## 参考文献

- nvim-treesitter（main ブランチ）, `lua/nvim-treesitter/install.lua`（e289100）. https://github.com/nvim-treesitter/nvim-treesitter/blob/e289100f/lua/nvim-treesitter/install.lua
- nvim-treesitter（main ブランチ）, README.md の Adding custom languages. https://github.com/nvim-treesitter/nvim-treesitter/blob/e289100f/README.md
