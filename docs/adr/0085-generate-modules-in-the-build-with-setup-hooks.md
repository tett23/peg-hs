# ADR 0085: 利用者のパッケージのビルドの中でモジュールを生成する

ステータス: 採択

## 文脈

peg-hs を使うには、今は `peg-hs` コマンドが要る。
利用者は `peg-hs gen` で文法からモジュールを生成し、生成したモジュールをコミットする（README）。
ライブラリとして依存するのは peg-runtime だけで、GitHub のタグを `source-repository-package` で指す（Hackage には上げていない、[ADR 0058](0058-no-hackage-candidates-for-pre-releases.md)）。
コマンドは、GitHub の Release の実行ファイルを入れるか、ソースからビルドして入れる。

作業者の指示で、コマンドを入れなくても、利用者の cabal パッケージのビルドの中で文法からモジュールを生成できるようにする。
peg-hs を、実行ファイルとしてだけでなく、ライブラリとしても使えるようにするためである。

どの仕組みで生成するかを決めるために、四つの候補を試作した（cabal-install 3.16.1.0、GHC 9.10.3、README の `Calc` の文法）。
試作はリポジトリの外で行い、peg-hs のパッケージをローカルのパスで指した。

- **`build-type: Hooks`**（Cabal 3.14 からの SetupHooks）：ビルドの前の規則（pre-build rule）で peg-codegen を呼び、autogen のディレクトリにモジュールを書く。動いた。
- **GHC のプリプロセッサ**（`{-# OPTIONS_GHC -F -pgmF ... #-}` と `build-tool-depends`）：動いた。しかし、古いモジュールのまま再ビルドされない場合が二つあった。
- **Template Haskell のスプライス**：生成したモジュールのテキストを宣言にするには、Haskell の構文解析器（haskell-src-meta か GHC API）が要る。スプライスは import と LANGUAGE プラグマを出せず、`{-# LINE #-}` も持てない。採れない。
- **`build-type: Custom` と `hookedPreProcessors`**：動いた。

### 試作でわかったこと

どの仕組みでも、文法のファイルを `extra-source-files` に書かないと、文法を変えても cabal が「Up to date」と言い、古いパーサーのままになった。

GHC 9.10.3 は、`{-# LINE #-}` プラグマが名前を挙げたファイルを、モジュールが依存するファイルとして `.hi` に記録する。
そのため、文法を変えると、生成したモジュールの内容が同じでも、GHC は `[grammar/Calc.hpeg changed]` としてモジュールをコンパイルし直した。

Hooks では、次のようになった。

- 何も変えないとき、文法のファイルの時刻だけを変えたとき（`touch`）は、「Up to date」だった。
- 文法を変えると、モジュールを生成し直し、コンパイルし直した。
- 文法と関係のない `Main.hs` を変えたときも、規則は生成をやり直した。生成したモジュールの内容は同じなので、GHC はコンパイルし直さなかった。
- アクションの型の誤りは、`grammar/Calc.hpeg:16:38: error: [GHC-83865] ...` と文法の位置で報告された。
- `cabal check` は、`Setup.hs` がないと `missing-setup` の誤りを出した。cabal が生成するのと同じ `Setup.hs`（`main = defaultMainWithSetupHooks setupHooks`）を置くと、消えた。
- `cabal sdist` の tarball には、文法と `SetupHooks.hs` が入り、生成したモジュールは入らなかった。
- GHC 9.10.3 に付属する Cabal は 3.12 なので、最初のビルドで Cabal 3.16.1.0 を Hackage のソースからビルドした。peg-hs のパッケージと合わせて、約 8 分 48 秒かかった。

プリプロセッサでは、次の二つの場合に古いモジュールのままになった。

- 生成したモジュールに `{-# LINE #-}` が一つもない文法（`%module G` と `A <- 'a'` だけの文法など）は、文法を変えてもコンパイルし直されなかった。
- 生成器のプリプロセッサを新しくビルドし直しても、利用者のモジュールは生成し直されなかった。

また、GHC は `-pgmF` に渡した文字列を一つの実行ファイルの名前として扱う（`-pgmF "./echo.sh pp"` は `could not execute` になった）。
そのため、`peg-hs gen` をそのままプリプロセッサにはできない。

Custom は、Hooks と同じく文法の変更で生成し直し、`Main.hs` の変更では生成し直さなかった（Cabal のプリプロセッサがファイルの時刻を比べる）。
しかし、Cabal User Guide は、Cabal 3.14 からカスタムの setup スクリプトを非推奨とし、Hooks を使うよう勧めている（「Deprecated since Cabal 3.14: prefer using the Hooks build type instead.」）。
試作では、cabal も `cabal check` も、Custom について警告を出さなかった。

Hooks を採る。
試作では古いモジュールが残る場合がなかった。
ビルドの規則として入力と出力を宣言でき、Cabal が Custom の代わりに勧める仕組みでもある。

## 実装すること

### パッケージ peg-hooks

新しいパッケージ peg-hooks を `packages/peg-hooks` に置く。
peg-runtime、peg-grammar、peg-codegen、peg-lsp、peg-cli と同じ版（0.1.0.0）で出す（[ADR 0044](0044-release-v0-1-0.md)）。
依存は、base、Cabal、Cabal-hooks、Cabal-syntax、directory、filepath、text、peg-grammar、peg-codegen とする。
Cabal と Cabal-hooks の範囲は、試作で使った 3.14 以上 3.17 未満とする。

公開するモジュールは `Peg.Hooks` とし、次を出す。

- `pegSetupHooks :: [Grammar] -> SetupHooks`：文法のそれぞれについて、ビルドの前の規則を一つ登録する。利用者は、この値を自分の `SetupHooks.hs` の `setupHooks` にする。ほかのフックと組み合わせるときは `<>` でつなぐ。
- `Grammar`：文法のファイルのパス（パッケージの根からの相対パス）と、生成するモジュールの名前の組。モジュールの名前は、文法の `%module` と一致しなければならない。一致しなければ、ビルドを誤りで止める。

規則は次のことをする。

- 入力として文法のファイルを宣言し、出力として autogen のディレクトリのモジュールのパスを宣言する。
- 文法を読み、`peg-hs gen` と同じ検査をして、モジュールを書く。生成したモジュールの `{-# LINE #-}` が指すファイル名は、パッケージの根からの相対パスとする。
- 誤りは `Peg.Grammar.renderDiagnostic` の形で標準エラーに出し、ビルドを止める。ラベルの警告（`labelWarnings`）は、`peg-hs gen` と同じ形で出し、ビルドは続ける。
- `--Werror`、`--strip-labels`、`--export`、`--debug-entry` に当たるものは、この ADR では出さない。

### 生成の手順の共有

`peg-hs gen` の手順（文法を読む、雛形を展開する、検査する、ラベルの警告を集める、生成する）は、今は peg-cli の実行ファイルの中（`app/Command/Gen.hs`）にある。
peg-hooks が同じ手順を使えるように、この手順のうち、ファイルの読み書きと終了状態を除いた部分を peg-codegen の公開の関数にする。
peg-cli の `gen` も、その関数を使うように書きかえる。
関数の名前と型は、実装で決め、Haddock に書く。

### 利用者が書くもの

README（日本語と英語）に、次の形を書く。

```cabal
cabal-version: 3.14
build-type:    Hooks
extra-source-files: grammar/Calc.hpeg

custom-setup
  setup-depends:
    , base
    , Cabal-hooks  >=3.14 && <3.17
    , peg-hooks    >=0.1  && <0.2

executable calc
  other-modules:   Calc.Parser
  autogen-modules: Calc.Parser
  build-depends:   base, peg-runtime >=0.1 && <0.2, text
```

```haskell
-- SetupHooks.hs
module SetupHooks (setupHooks) where

import Distribution.Simple.SetupHooks (SetupHooks)
import Peg.Hooks (Grammar (..), pegSetupHooks)

setupHooks :: SetupHooks
setupHooks = pegSetupHooks [Grammar "grammar/Calc.hpeg" "Calc.Parser"]
```

あわせて、`cabal check` のために `Setup.hs` を置くこと、文法を `extra-source-files` に書かないと文法の変更でモジュールが作り直されないこと、`cabal.project` の `source-repository-package` に peg-hooks、peg-codegen、peg-grammar も書くこと、最初のビルドで Cabal をビルドするので時間がかかることを書く。
上の断片の正確な形（`Grammar` の書き方、`setup-depends` に要るもの）は、実装で動かしたものに合わせる。

コマンドで生成してコミットする今の使い方は、そのまま残す。
README には、二つの使い方の違い（生成物をコミットするか、ビルドのたびに作るか）を書く。

### 配布と CI

- リリースのワークフローは、peg-hooks の sdist と Haddock の tarball も Release に添付する。
- CI に、peg-hooks を使う小さな利用者のパッケージ（`examples/hooks/`）をビルドして動かすジョブを足す。
- `docs/specifications.md` にパッケージの一覧と、ビルドの中での生成を書く。CONTRIBUTING のパッケージの一覧にも足す。

## 実装しないこと

- GHC のプリプロセッサの形。古いモジュールが残る場合があるからである。
- Template Haskell のスプライス。Haskell の構文解析器が要るからである。
- `build-type: Custom` の形。Cabal が非推奨としているからである。
- Hackage への公開。[ADR 0058](0058-no-hackage-candidates-for-pre-releases.md) のとおり、rc の間は上げない。
- stack への対応の確かめ。手元に stack がなく、試していない。
- 文法の `%module` からモジュールの名前を自動で決めること。規則は出力のパスを実行の前に宣言しなければならず、利用者は `.cabal` の `autogen-modules` にも名前を書くので、`Grammar` に書かせる。
- 生成器の版が変わったときの生成し直しの確かめ。peg-hooks の版が変わると `Setup` がビルドし直されるはずだが、試作では確かめていない。実装で確かめ、確かめられなければトレードオフに書く。

## テスト設計

先に書いて失敗させてから実装する。

- `examples/hooks/` に、README の `Calc` の文法で式を解析する実行ファイルのパッケージを置く。CI のジョブでビルドし、`1 + 2 * 3` を解析した結果を確かめる。
- 同じジョブで、次の再ビルドの振る舞いをシェルスクリプトで確かめる。スクリプトは、作業用の写しの中で文法を書きかえる。
  - 何も変えずにビルドすると、モジュールを生成しない（ビルドの出力に生成の行が出ない、または GHC が `Calc.Parser` をコンパイルしない）。
  - 文法の意味を変えると、モジュールが生成し直され、解析の結果が変わる。
  - 文法に誤りを入れると、ビルドが失敗し、`renderDiagnostic` の形の誤り（`grammar/Calc.hpeg:行:桁: error: ...`）が出る。
  - アクションに型の誤りを入れると、GHC の誤りが文法の位置を指す。
  - `Grammar` のモジュールの名前を `%module` と違うものにすると、ビルドが失敗する。
- 試作では、規則とそのコマンドを利用者の `SetupHooks.hs` の中に書いた。peg-hooks では、規則のコマンドの static pointer が別のパッケージにある。`examples/hooks/` のビルドが通ることで、この形が動くことを確かめる。あわせて、`pegSetupHooks` を利用者の別のフックと `<>` でつないでも、両方のフックが動くことを確かめる。
- peg-codegen に移した生成の手順は、peg-cli の `gen` のテスト（golden とラベルの警告、`--Werror`）が今までどおり通ることで確かめる。
- `examples/hooks/` で `cabal check` と `cabal sdist` を実行し、`cabal check` が誤りを出さないこと、tarball に生成したモジュールが入らないことを確かめる。

## トレードオフ

- 利用者は `cabal-version: 3.14` 以上と、Cabal 3.14 以上を setup の依存として使える cabal-install が要る。GHC 9.10 に付属する Cabal は 3.12 なので、最初のビルドで Cabal をビルドし、時間がかかる（試作で約 9 分）。
- 文法と関係のない変更でも、規則は生成をやり直す。生成したモジュールの内容が同じなら GHC はコンパイルし直さないので、かかるのは生成の時間だけである。
- 生成したモジュールをコミットしないので、利用者のリポジトリで生成物の差分をレビューできない。生成物を見たいときは、今までどおりコマンドで生成してコミットする使い方を選ぶ。
- パッケージが六つになり、リリースと版の管理の手間が増える。
- 文法を `extra-source-files` に書き忘れると、古いモジュールのままになる。cabal の仕組みなので peg-hooks からは防げない。README に書いて防ぐ。

## 参考文献

- Cabal User Guide, "Package Description" の "build-type" と "custom-setup". https://cabal.readthedocs.io/en/stable/cabal-package-description-file.html
- Cabal-hooks（Hackage）. https://hackage.haskell.org/package/Cabal-hooks
- GHC User's Guide, "Options affecting a Haskell pre-processor". https://downloads.haskell.org/ghc/latest/docs/users_guide/phases.html
