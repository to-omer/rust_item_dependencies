# 利用ガイド

## 必要なもの

Rust、Cargo、Git、Pythonと、Rustコンパイラをビルドできる環境が必要です。初回はRustのソースコードを取得するため、ネットワークへ接続します。ホストのOSとCPUは自動で判定されるため、実行するコマンドは共通です。

## コードを削減する

入力ファイルと出力先を指定して、リポジトリのルートで実行します。

```console
cargo rid input.rs -o reduced.rs
```

初回は、このツールが利用するRustコンパイラを取得してビルドします。2回目以降は同じコンパイラを再利用します。

入力ファイルと同じパスや、すでに存在するファイルを出力先に指定することはできません。

## オプション

`-o`では出力先を指定します。この指定は必須です。

`--edition`ではRustのエディションを指定します。省略時は2024です。

```console
cargo rid --edition 2021 input.rs -o reduced.rs
```

`--target`ではコンパイル対象を指定します。省略時は、現在のホストと同じコンパイル対象を使います。指定先の標準ライブラリが、ツールのコンパイラに導入されている必要があります。

`-O`では最適化レベル`3`を指定します。別のレベルを使う場合は、`--opt-level`で`0`、`1`、`2`、`3`、`s`、`z`のいずれかを指定します。省略時は`0`です。最適化オプションを複数指定した場合は、最後の指定を使います。`debug_assertions`は、指定した最適化レベルに基づいてRustコンパイラが決めます。

`--cfg`では、値を持たない`cfg`名を有効にします。複数の名前を有効にする場合は、`--cfg NAME`を繰り返します。`feature="name"`のような値付き`cfg`には対応していません。

外部クレートを使う場合は、入力から直接参照するクレートを`--extern NAME=PATH`で指定します。そのクレートが別のクレートへ依存している場合は、推移的な依存先を`--dependency-artifact PATH`で指定します。どちらも必要な数だけ繰り返せます。通常のライブラリには`.rlib`を指定します。

依存クレートは`cargo rid rustc`でビルドします。たとえば、`wrapper`が`leaf`に依存する場合は、次の順に実行します。

```console
cargo rid rustc leaf.rs --crate-name leaf --crate-type rlib --edition 2024 -o target/libleaf.rlib
cargo rid rustc wrapper.rs --crate-name wrapper --crate-type rlib --edition 2024 --extern leaf=target/libleaf.rlib -o target/libwrapper.rlib
cargo rid --extern wrapper=target/libwrapper.rlib --dependency-artifact target/libleaf.rlib input.rs -o reduced.rs
```

`cargo rid rustc`の後ろに指定した引数は、削減に使う専用コンパイラへそのまま渡されます。別のコンパイル対象を指定する場合は、依存クレートのビルドと削減のすべてに同じ`--target`を指定してください。このツールは`Cargo.toml`を読まず、依存クレートや`build.rs`を自動ではビルドしません。

### 手続きマクロ

手続きマクロを使う場合は、コンパイラを実行するホスト向けにビルドした動的ライブラリを指定します。入力から直接参照する場合は`--extern`、別のクレートから再公開される場合は`--dependency-artifact`へ指定してください。さらに、同じ成果物を`--allow-proc-macro`で明示的に許可します。

```console
cargo rid --extern my_macro=PATH_TO_PROC_MACRO --allow-proc-macro PATH_TO_PROC_MACRO input.rs -o reduced.rs
```

`PATH_TO_PROC_MACRO`には、専用コンパイラと互換性のある手続きマクロ成果物のパスを指定します。手続きマクロは`cargo rid rustc macro.rs --crate-name my_macro --crate-type proc-macro -o PATH_TO_PROC_MACRO`でビルドできます。手続きマクロはホストで実行するため、このビルドには入力プログラム用の`--target`を指定しません。

許可した手続きマクロは、このツールと同じ権限で動くネイティブコードです。信頼できる成果物だけを許可してください。手続きマクロがファイル、環境変数、時刻、ネットワークなどを参照する場合、その状態が解析中に変わらないことは利用者が保証する必要があります。

## 対応するコード

対象は、安定版Rustで書かれた、1ファイルの通常の実行プログラムです。ビルド済みのRustライブラリと、明示的に実行を許可した手続きマクロは依存先として指定できます。別途ネイティブライブラリを必要とする依存先には対応していません。詳しい入力条件と削減ルールは[詳細仕様](specification.md)を参照してください。
