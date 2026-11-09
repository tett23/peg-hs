# ADR 0093: UTF-8 のバイト列を入力の Text に直す関数を peg-runtime に置く

ステータス: 採択（未実装）

## 文脈

生成したモジュールの入口は `Text` を受け取る（`parse :: Text -> Either ParseError a`。[ADR 0014](0014-generated-module-api.md)）。
ファイルやネットワークから届く入力はバイト列なので、利用者は入口を呼ぶ前にそれを `Text` に直す。
[ADR 0014](0014-generated-module-api.md) は、`String` や `ByteString` を受け取る入口を「実装しないこと」に挙げた。
[ADR 0045](0045-fixes-before-v0-1-0.md) も、ファイルをどう読むかは利用者に任せると決めた。

任された利用者の手元には、手軽だが危うい道が二つある。

一つめは `Data.Text.IO` である。
README の「Using a generated module」の例は `TIO.getLine` で、`Peg.Runtime` の Haddock の例は `TIO.getContents` で入力を読む。
`Data.Text.IO` はロケールの文字コードで読むので、Linux の C ロケールでは日本語を含む入力の読み込みに失敗する見込みがある（[ADR 0045](0045-fixes-before-v0-1-0.md) の文脈）。
peg-hs 自身は [ADR 0045](0045-fixes-before-v0-1-0.md) でこの問題を避けたが、生成したモジュールの利用者には同じ避け方が示されていない。

二つめは `Data.Text.Encoding` である。
`decodeUtf8` は、UTF-8 として正しくない入力で例外を投げる部分関数である。
全域の `decodeUtf8'` は誤りを `UnicodeException` で返すが、この型は誤りのバイトの値を持つだけで、位置を持たない。
text 2.1.3 の `UnicodeException` の構築子は `DecodeError String (Maybe Word8)` と `EncodeError String (Maybe Char)` である。
バイト列 `61 FF 62` を `decodeUtf8'` に渡すと、`Cannot decode byte '\xff': Data.Text.Encoding: Invalid UTF-8 stream` が返り、何バイトめかはわからない。
先頭のバイト順マーク（BOM）も、`decodeUtf8'` は取り除かず U+FEFF として残す。
文法の先頭が U+FEFF を受け付けなければ、解析は 1 行 1 桁で失敗する。

peg-hs の側には、すでに正しい手順がある。
`peg-hs` は、ファイルをバイト列で読み、先頭の BOM を読み飛ばし、UTF-8 として正しくなければ失敗したバイトの位置を報告する（`packages/peg-cli/app/FileIO.hs` の `decodeUtf8File`）。
ただし、これは peg-cli の実行ファイルの中の関数で、利用者は呼べない。

### peg-runtime の入力と位置

peg-runtime は、入力を text 2 の `Text` のまま扱う。
text 2 の `Text` は内部の表現が UTF-8 であり、peg-runtime はそのバイトを直接読む（`Peg.Runtime.Internal` の `TU.lengthWord8`、`TU.iter`、`Data.Text.Array`）。
`Pos` の `posOffset` は UTF-8 のバイトオフセット、`posLine` は LF で数える 1 から始まる行、`posColumn` は符号位置で数える 1 から始まる桁である（[ADR 0008](0008-source-positions.md)、[ADR 0014](0014-generated-module-api.md)）。
桁は `%tabstop` の影響を受けない。
したがって、入力のバイト列が UTF-8 として正しく、BOM を除いたものであれば、`Text` のバイトオフセットは元のバイト列のオフセットと一致する。
位置の表現は、バイト列の入力のために変える必要がない。

### text と bytestring で確かめたこと

GHC 9.10.3 と 9.14.1 に付属する text は、どちらも 2.1.3 で、bytestring 0.12.2.0 に依存する（`ghc-pkg field text version,depends`）。
このリポジトリのビルドの計画（`dist-newstyle/cache/plan.json`）でも、text は 2.1.3、bytestring は 0.12.2.0 である。
peg-runtime に bytestring の依存を足しても、ビルドに加わるパッケージは増えない。
peg-grammar、peg-lsp、peg-cli は、すでに `bytestring >=0.11 && <0.13` に依存している。

text 2.1.3 の `decodeUtf8With` は、正しい入力では検証の後に `Data.ByteString.Short.toShort` で `Text` を作る（`src/Data/Text/Internal/Encoding.hs` の `decodeUtf8With1`）。
bytestring 0.12.2.0 の `toShort` の Haddock は「This makes a copy」と書く。
よって、`decodeUtf8'` は検証に一度、写しに一度、入力を読む。
写しを避けて `ByteString` の領域をそのまま `Text` にする公開の関数は、text 2.1.3 の `Data.Text.Encoding` に見当たらない。

text 2.0.2 から、`Data.Text.Encoding` は `validateUtf8Chunk :: ByteString -> (Int, Maybe Utf8State)` を公開している。
一つめの値は、正しい UTF-8 として読めた接頭辞のバイト数である。
GHC 9.10.3 で次のバイト列を渡して確かめた。

| バイト列 | 一つめの値 | 二つめの値 |
|---|---|---|
| `61 62` | 2 | `Just` |
| `61 FF 62` | 1 | `Nothing` |
| `61 E0 41` | 1 | `Nothing` |
| `61 E3 81`（末尾で切れた 3 バイトの列） | 1 | `Just` |
| `61 ED A0 80`（サロゲート） | 1 | `Nothing` |
| `61 C0 AF`（冗長な表現） | 1 | `Nothing` |
| `61 E3 81 82 80` | 4 | `Nothing` |
| `EF BB BF 61` | 4 | `Just` |

一つめの値がバイト列の長さより小さいとき、それは正しくない列の先頭のバイトのオフセット（0 から）である。
末尾で切れた列は二つめの値が `Just` だが、一つめの値が長さに届かないことで見分けられる。
この値は、`peg-hs` の `decodeUtf8File` が報告する位置（1 から数えるので、1 を足したもの）と、上の例ではすべて一致する。

### 検討した形

選択肢は二つあった。

- 生成する入口を増やす：`%entry` ごとに `parseUtf8 :: ByteString -> Either ... a` のような入口を足す
- peg-runtime に関数を置く：バイト列を `Text` に直す関数を一つ置き、利用者はそれを通してから今の入口を呼ぶ

生成する入口を増やすと、入口の数が掛け算で増える。
一つの文法が持ちうる入口は、開始規則と `%entry` の規則のそれぞれに、`parse`、`parseSyntax`、`parseRecover`、`parseSyntaxRecover` の形がある。
入力の型ごとにこれを複製すると、生成するモジュールと `--export` の名前（[ADR 0061](0061-select-generated-exports.md)）が倍になる。
しかも、増えた入口がすることは、どれも「直してから今の入口を呼ぶ」だけである。
この前処理は文法によらないので、生成器が文法ごとに書き出す理由がない。

UTF-8 の誤りの型も、生成する入口に向かない。
`ParseError` は、最遠到達位置、期待集合、ラベルを持つ（[ADR 0005](0005-error-reporting.md)、[ADR 0021](0021-error-recovery.md)）。
UTF-8 の誤りをこの型に入れると、期待集合は空になり、`renderParseError` は `parse error` と書く。
文法の失敗と入力の文字コードの誤りが同じ文で表示され、利用者は区別できない。
ラベルに予約の名前を入れる手もあるが、利用者のラベルと名前の空間を分け合うことになる。
入口の型を `Either (Either Utf8Error ParseError) a` のように変えれば区別はできるが、それでは前処理の関数の戻り値を入口の型に埋め込んだだけである。

そこで、peg-runtime に関数を置く形を選ぶ。
[ADR 0014](0014-generated-module-api.md) の「`String` や `ByteString` を受け取る入口」を実装しない決定は、そのまま保つ。

## 実装すること

### API

`Peg.Runtime` に次の二つの関数と一つの型を加える。

```haskell
-- | The input text of UTF-8 bytes, without a byte order mark at the start.
decodeInput :: ByteString -> Either Utf8Error Text

-- | Bytes that are not UTF-8.
newtype Utf8Error = Utf8Error
  { utf8ErrorPos :: Pos
  -- ^ The position of the first byte of the first ill-formed sequence.
  }
  deriving (Eq, Show)

-- | Render an error as @line:column: invalid UTF-8@.
renderUtf8Error :: Utf8Error -> Text
```

`decodeInput` の振る舞いは次のとおりとする。

- 先頭の 3 バイトが BOM（`EF BB BF`）なら、それを除いてから残りを扱う。先頭以外の `EF BB BF` は U+FEFF として残す
- 残りが UTF-8 として正しければ、それを `Text` にして返す。正しさの基準は text の検証と同じで、冗長な表現、サロゲート、U+10FFFF より大きい符号位置、末尾で切れた列を誤りとする
- 正しくなければ、最初の正しくない列の先頭のバイトの位置を `Utf8Error` で返す。末尾で切れた列は、その列の先頭のバイトの位置とする

`utf8ErrorPos` の数え方は、`ParseError` の `Pos` と同じである。
`posOffset` は BOM を除いた後のバイト列での 0 から始まるオフセット、`posLine` と `posColumn` は、そのオフセットまでの正しい接頭辞から数える。
BOM で始まる入力では、`posOffset` は元のバイト列のオフセットより 3 小さい。
`decodeInput` が返した `Text` を入口に渡したときの `ParseError` の位置も、同じく BOM を除いた後で数えるので、二つの誤りの位置は同じ座標で読める。

`renderUtf8Error` は `行:桁: invalid UTF-8` の一行を返す。
`renderParseError` の `行:桁: expected ...` と同じ形にそろえる。

### 実装の置き場所と依存

- 関数と型は、peg-runtime の公開しないモジュール `Peg.Runtime.Input` に置き、`Peg.Runtime` から再エクスポートする。`Peg.Runtime.Internal` には加えない。生成したモジュールとの約束（[ADR 0046](0046-docs-cli-and-ci-before-v0-1-0.md)）は変わらない
- 変換は text の `decodeUtf8'` で行う。`Left` のときだけ、`validateUtf8Chunk` で正しい接頭辞の長さを求め、その接頭辞から `Peg.Runtime.Position` の `lineIndex` と `posIn` で位置を求める。正しい入力の検証は一度で済む
- peg-runtime の `build-depends` に `bytestring >=0.11 && <0.13` を加え、text の下限を `validateUtf8Chunk` のある `>=2.0.2` に上げる
- 変更は関数と型の追加なので、PVP の上ではマイナーの変更である。生成したモジュールの先頭に書く peg-runtime の範囲（`>=0.1 && <0.2`）は変えない。`decodeInput` を呼ぶ利用者は、それを加えた版を下限にする
- `peg-hs parse` は peg-runtime のソースを埋め込んでコンパイルする（`packages/peg-cli/app/Embedded.hs`）。`scripts/regen-fixtures.sh` で埋め込みを作り直す

### 文書

- `Peg.Runtime` の Haddock の例を、`Data.ByteString` で標準入力を読み、`decodeInput` を通してから `parse` を呼ぶ形に変える
- README（英語と日本語）の「Using a generated module」の節に、ファイルを読む場合の短い例を加える。`BS.readFile` で読み、`decodeInput` の誤りを `renderUtf8Error` で、解析の誤りを `renderParseError` で表示する。節の先頭にある、コンパイルして動かすことを確かめる例（`<!-- readme-example: src/Main.hs -->`）は変えない
- README の「Known limitations」の Encoding の項に、生成したモジュールの利用者は `decodeInput` で UTF-8 のバイト列を `Text` にできることを書き足す
- 仕様書の「生成するコード」に、入口は `Text` だけを受け取り、バイト列は peg-runtime の `decodeInput` で直すことを、この ADR へのリンクつきで書く
- peg-runtime の `CHANGELOG.md` に追加を書く

## 実装しないこと

- バイト列を受け取る生成の入口（`parseUtf8` など）。[ADR 0014](0014-generated-module-api.md) の決定を保つ
- `String` を受け取る入口と関数。`T.pack` で足りる
- 遅延の `Data.Text.Lazy.Text` と `Data.ByteString.Lazy.ByteString` の入力。入力は全体をメモリに載せた `Text` とし、ストリーミングパースはしない（仕様書の「意図的に採用しなかったもの」）。遅延のバイト列は、利用者が `toStrict` で直してから渡す
- 写しを避けた変換。text 2.1.3 の公開の API では、検証した `ByteString` の領域を写さずに `Text` にできない。入力全体を一度写す費用は、解析の費用に比べて小さいと見込む
- UTF-8 以外の文字コード（UTF-16、Latin-1 など）の変換。ロケールに従う文字コードも扱わない（[ADR 0045](0045-fixes-before-v0-1-0.md)）
- 正しくないバイトを U+FFFD に置きかえて続ける変換。必要なら、利用者が `decodeUtf8Lenient` を使う
- 2 番め以降の誤りの報告。最初の誤りだけを返す
- `peg-hs` の `decodeUtf8File` を `decodeInput` で置きかえること。CLI の誤りは、[ADR 0045](0045-fixes-before-v0-1-0.md) の形（`not UTF-8 (at byte N)`、BOM を含む元のファイルの 1 から数える位置）を保つ
- `peg-hs parse` が生成する主モジュールの変更。入力は CLI が先に検証している
- wasm（[ADR 0078](0078-grammar-analysis-in-wasm.md)）の変更。wasm は文法を扱い、入力のテキストを解析しない

## テスト設計

先に書き、失敗させてから実装する。
peg-runtime のテスト（`packages/peg-runtime/test/Main.hs`）に置き、テストの `build-depends` に bytestring を加える。
テストは `Peg.Runtime` から `decodeInput`、`Utf8Error (..)`、`renderUtf8Error` を import するので、実装の前はコンパイルに失敗する。

### 単体のテスト

- 空のバイト列は `Right ""` になること
- ASCII と、日本語を含むバイト列（`T.encodeUtf8` で作る）が、元の `Text` に戻ること
- BOM で始まるバイト列 `EF BB BF 61` が `Right "a"` になること。BOM だけのバイト列が `Right ""` になること
- 先頭以外の BOM（`61 EF BB BF`）が U+FEFF として残ること
- 文脈の表の正しくない 6 例が、それぞれ `posOffset` 1、`posLine` 1、`posColumn` 2 の `Utf8Error` になること。`61 E3 81 82 80` は `posOffset` 4、`posColumn` 3 になること
- 行をまたぐ場合：`a\nあ` の後に `FF` を続けたバイト列が、`Pos 5 2 2` になること（`あ` は 3 バイトで 1 桁）
- BOM の後の誤り：`EF BB BF 61 FF` が `posOffset` 1 になること
- タブを含む行：`\tx` の後の `FF` が `posColumn` 3 になること（`%tabstop` によらず、タブは 1 桁）
- `renderUtf8Error` が `Pos 5 2 2` の誤りを `2:2: invalid UTF-8` と書くこと

### 性質のテスト

QuickCheck で、任意のバイト列と、UTF-8 として正しい列に任意のバイトを差し込んだ列を生成する。
後者を混ぜるのは、一様なバイト列はほとんどが最初の数バイトで正しくなくなり、正しい場合を十分に試せないためである。

- `decodeInput` が `Right` を返すことと、BOM を除いたバイト列に `decodeUtf8'` が `Right` を返すことが一致すること
- `Right t` のとき、`T.encodeUtf8 t` が BOM を除いたバイト列と等しいこと
- `Left e` のとき、`n = posOffset (utf8ErrorPos e)` について、BOM を除いたバイト列の先頭 `n` バイトは `decodeUtf8'` で `Right` になり、先頭 `n + k` バイト（`k` は 1 から 4）は `Left` になること。`n` が正しい接頭辞の最長の長さであることを示す
- `Left e` のとき、`posLine` と `posColumn` が、先頭 `n` バイトを `Text` にしたものの LF の数と最後の LF の後の符号位置の数から求めた値と一致すること

### 既存のテスト

- peg-codegen の golden のテストが、生成したモジュールの変化なしで通ること。生成器は変えない
- peg-cli の、埋め込んだ peg-runtime のソースが `packages/peg-runtime/src` と一致することのテストが、`scripts/regen-fixtures.sh` の後に通ること。あわせて、`peg-hs parse` のテストが、`bytestring` を import する peg-runtime のソースで通ること
- README の例のテスト（[ADR 0045](0045-fixes-before-v0-1-0.md)）が変わらず通ること

## トレードオフ

- 利用者は、バイト列を解析するときに二つの関数を呼び、二つの誤りの型を扱う。一つの入口で済む形に比べて手数が増える。その代わり、生成する入口の数と生成器は変わらず、二つの誤りは型で区別できる
- peg-runtime が bytestring に直接依存する。text が bytestring に依存しているので、ビルドに加わるパッケージは増えない。peg-runtime の依存の一覧には一行増える
- text の下限を 2.0.2 に上げる。2.0.0 と 2.0.1 の text は使えなくなる。GHC 9.10.3 と 9.14.1 は text 2.1.3 を付属することを確かめた。9.12 は手元になく、確かめていない
- BOM を黙って除くので、BOM で始まる入力の `posOffset` は、元のバイト列のオフセットと 3 ずれる。`peg-hs` の CLI の誤りは元のファイルのバイトで数えるので、同じファイルでも CLI とライブラリで数え方が異なる。ライブラリの側は、解析の誤りと同じ座標にそろえることを優先した
- 入力全体の写しが一度できる。入力の大きさの分だけメモリを一時に余分に使う

## 参考文献

- text 2.1.3 のソース。`src/Data/Text/Encoding.hs`（`decodeUtf8'`、`decodeUtf8`）、`src/Data/Text/Internal/Encoding.hs`（`validateUtf8Chunk`、`decodeUtf8With1`）、`src/Data/Text/Encoding/Error.hs`（`UnicodeException`）。https://github.com/haskell/text/tree/2.1.3
- bytestring 0.12.2.0 のソース。`Data/ByteString/Short/Internal.hs`（`toShort`）。https://github.com/haskell/bytestring/tree/0.12.2.0
- The Unicode Standard, 3.9 Unicode Encoding Forms, Table 3-7 Well-Formed UTF-8 Byte Sequences（`packages/peg-cli/app/FileIO.hs` の `utf8ErrorOffset` が従う表）
