# rust-item-dependencies

`rust-item-dependencies`は、1ファイルのRustプログラムから実行に不要なコードを取り除くツールです。名前解決、型の選択、マクロ展開など、コンパイラが確定した依存関係をもとに残すコードを判断します。

## 使い方

[インストール](docs/README.md#インストール)後、対象のCargoプロジェクトで実行します。

```console
cargo rid
```

Cargoの設定で選ばれる実行プログラムを削減し、検証に成功した結果でソースファイルを更新します。複数の候補がある場合は`--package`や`--bin`で選びます。対象ソースは1ファイルに収まっている必要があります。

独立したソースファイルには`cargo rid input.rs`を使えます。初回は専用のRustコンパイラを`target/`配下に用意するため、完了まで時間がかかります。

専用コンパイラのビルドを省く場合は、[Docker版](docs/README.md#dockerで使う)を利用できます。

## ドキュメント

- [利用ガイド](docs/README.md)
- [詳細仕様](docs/specification.md)
