# ADR 0079: 約束の外の WASI の import を wasm の中の関数で置きかえる

ステータス: 採択

## 文脈

[ADR 0078](0078-grammar-analysis-in-wasm.md) は、`peg-grammar`、`peg-codegen`、`peg-lsp` を GHC の wasm バックエンドで reactor にし、ページ側と import の約束を決めた。
import してよいのは `wasi_snapshot_preview1` の次の関数だけである。

- `args_get`、`args_sizes_get`、`environ_get`、`environ_sizes_get`
- `clock_time_get`、`clock_res_get`、`random_get`
- `fd_write`（標準出力と標準エラーだけ）、`proc_exit`

[ADR 0078](0078-grammar-analysis-in-wasm.md) は、実装でこの一覧を超える import が見つかったら実装を止め、どうするかを別の ADR で決める、としていた。
この ADR がそれである。

実装の最初に、ghc-wasm-meta の flake（コミット `8079eb96bbc63823d99ad8acaff0765532625474`、出力 `all_9_10`、GHC 9.10.3.20260731）で、最小の reactor をビルドした。
`analyze` と `format` をエクスポートし、`generateFromSource`、`formatGrammar`、`Peg.Lsp.Json` を呼ぶものである。
依存はどれも wasm でビルドでき、wasm は 7,208,856 バイトになった。

import は 18 個あり、そのうち 13 個が約束の外だった。

- `fd_close`、`fd_fdstat_get`、`fd_fdstat_set_flags`、`fd_filestat_get`、`fd_filestat_set_size`
- `fd_prestat_get`、`fd_prestat_dir_name`、`fd_read`、`fd_seek`
- `path_create_directory`、`path_filestat_get`、`path_open`、`poll_oneoff`

ファイルとポーリングの関数である。
GHC のランタイムと C ライブラリが、ファイルの入出力のために持っているものと考えられる。

これらが実行のときに呼ばれるかを、Deno で測った。
すべての import に呼ばれた回数を数える関数を渡し、約束の外の 13 個は何もせずに誤りを返すようにした。
初期化（`_initialize`、`hs_init(0, 0)`）、`conformance/bench/JsonGenerated.hpeg` の `analyze` と `format`、未定義の規則を参照する文法の `analyze`、`analyze` の 50 回の繰り返しのあいだに呼ばれたのは、`environ_sizes_get`（初期化で 1 回）と `clock_time_get` だけだった。
約束の外の関数は、一度も呼ばれなかった。

呼ばれないとしても、import は残る。
`WebAssembly.Instance` は、import がすべてそろわなければ wasm を作れない。
このままでは、約束の範囲だけを実装したページ側の WASI では、wasm を読み込めない。

直し方は二つあった。
ページ側に、約束の外の関数を誤りを返すだけの関数として足してもらう方法と、wasm の側で import を消す方法である。
前者はページ側の ADR と実装を変える。
後者は、ビルドの後に一手順を足すだけで、約束を変えない。
後者を選んだ。

wasm の側で import を消せることは、試して確かめた。
ツールチェーンの binaryen（version 133）の `wasm-merge` は、二つの wasm を一つにし、片方の import を、もう片方のエクスポートで埋める。
約束の外の 13 個を持つ小さな wasm を `wasi_snapshot_preview1` という名前で合わせると、import は 5 個（`environ_get`、`environ_sizes_get`、`clock_time_get`、`fd_write`、`proc_exit`）になった。
合わせた wasm は、13 個の関数をエクスポートにも持つ。
これは binaryen の `wasm-metadce` で、残すエクスポートを根にした到達の解析をすると消えた。
最後の wasm は 5,084,125 バイトで、エクスポートは [ADR 0078](0078-grammar-analysis-in-wasm.md) の表の 7 個だけになった。
この wasm に、約束の 5 個の関数だけを渡して読み込むと、上と同じ呼び出しがすべて同じ応答を返した。

## 実装すること

### 置きかえる関数

`wasm/stubs.wat` に、約束の外の 13 個の関数を、WASI preview1 の型のまま書く。
どの関数も引数を読まず、すぐに誤りの番号を返す。

| 関数 | 返す値 |
| --- | --- |
| `fd_prestat_get` | `8`（`EBADF`） |
| ほかの 12 個 | `52`（`ENOSYS`） |

`fd_prestat_get` は、その番号に前もって開いたディレクトリがあるかを問う関数である。
前もって開いたディレクトリは一つもないので、ほかの関数と違って「機能がない」ではなく、使われていない番号を表す `EBADF` を返す。
ほかの関数は、その機能がないことを `ENOSYS` で伝える。

### ビルドの後の手順

`scripts/build-wasm.sh`（POSIX の sh）を置き、CI、リリース、手元のどれでも、これで wasm を作る。
スクリプトは、ghc-wasm-meta の道具が `PATH` にあることを前提にする。
手順は次のとおりである。

1. `wasm32-wasi-cabal build --project-file=cabal.project.wasm exe:peg-hs-wasm` でビルドする。
2. `wasm-tools parse wasm/stubs.wat` で、置きかえる関数の wasm を作る。
3. `wasm-merge` で、ビルドした wasm と置きかえる関数の wasm を合わせる。置きかえる関数の wasm の名前は `wasi_snapshot_preview1` とする。
4. `wasm-metadce` で、`wasm/exports.json` に書いたエクスポート（[ADR 0078](0078-grammar-analysis-in-wasm.md) の表の 7 個）を根にして、ほかのエクスポートを消す。
5. 結果を、引数に渡したパス（リリースでは `peg-hs.wasm`）に書く。

[ADR 0078](0078-grammar-analysis-in-wasm.md) の CI の `wasm` ジョブと、リリースの `wasm` ジョブは、このスクリプトを使う。

### 文書

README の wasm の節に、約束の外の関数を wasm の中の関数で置きかえていることと、それらが返す値を書く。
`docs/specifications.md` の wasm の項にも書く。

## 実装しないこと

- ページ側の WASI の実装の変更。約束は [ADR 0078](0078-grammar-analysis-in-wasm.md) のとおりで変えない。
- 置きかえる関数を、ファイルの入出力として動かすこと。peg-hs の wasm はファイルを読み書きしない。
- `wasm-opt` による縮小。[ADR 0078](0078-grammar-analysis-in-wasm.md) のとおり、大きさと読み込みの時間を測ってから決める。

## テスト設計

[ADR 0078](0078-grammar-analysis-in-wasm.md) のテスト設計に、次を足す。
[ADR 0078](0078-grammar-analysis-in-wasm.md) の wasm のテストは、この ADR の手順の後の wasm で動かす。

- 置きかえる関数の一覧
  - `wasm/stubs.wat` のエクスポートが、ビルドした直後の wasm（手順 1 の結果）の import から、約束の関数を除いたものと一致する。GHC やツールチェーンを上げて import が増えたり減ったりしたら、このテストが落ちる。
- 手順の後の wasm
  - import が、約束の一覧に含まれる関数だけである（[ADR 0078](0078-grammar-analysis-in-wasm.md) のテスト）。
  - エクスポートが、[ADR 0078](0078-grammar-analysis-in-wasm.md) の表の 7 個とちょうど一致する。置きかえる関数のエクスポートが残っていない。
  - テストのための WASI は、約束の関数だけを持つ（[ADR 0078](0078-grammar-analysis-in-wasm.md) のとおり）。この WASI で読み込めて、[ADR 0078](0078-grammar-analysis-in-wasm.md) の wasm のテストがすべて通る。

`build-wasm.sh` の手順そのものは、CI の `wasm` ジョブが毎回動かすことで確かめる。

## トレードオフ

- いまのコードは約束の外の関数を呼ばないが、将来のコードが呼ぶかもしれない。その場合、ページを止める代わりに、Haskell の側で入出力の誤りになる。`analyze` と `format` はその例外を捕まえて `{"error": ...}` を返すので（[ADR 0078](0078-grammar-analysis-in-wasm.md)）、wasm は動き続ける。ただし、呼ばれたことには、応答の誤りを見るまで気付けない。
- ビルドに三つの道具（`wasm-tools`、`wasm-merge`、`wasm-metadce`）を使う手順が増える。どれも [ADR 0078](0078-grammar-analysis-in-wasm.md) で固定した ghc-wasm-meta の flake に入っているので、新しい依存はない。
- 置きかえる関数の一覧を手で持つ。ツールチェーンを上げて import が変わると、一覧を直す必要がある。テストが一覧のずれを検出する。

## 参考文献

- [ADR 0078](0078-grammar-analysis-in-wasm.md)
- ghc-wasm-meta, README（コミット `8079eb96bbc63823d99ad8acaff0765532625474`、2026-10-12）. https://gitlab.haskell.org/haskell-wasm/ghc-wasm-meta
- binaryen, `wasm-merge --help` と `wasm-metadce --help`（version 133）
