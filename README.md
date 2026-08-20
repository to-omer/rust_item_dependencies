# rust-item-dependencies

`rust-item-dependencies`は、1ファイルのRustプログラムから実行に不要なコードを取り除くツールです。名前解決、型の選択、マクロ展開など、コンパイラが確定した依存関係をもとに残すコードを判断します。

## すぐ試す

リポジトリのルートで次を実行します。

```console
cargo rid tests/fixtures/compiler/driver_smoke.rs -o target/reduced.rs
```

削減後のコードは`target/reduced.rs`に保存されます。入力ファイルは変更しません。初回だけ専用のRustコンパイラを`target/`配下に用意するため、完了まで時間がかかります。

## ドキュメント

- [利用ガイド](docs/README.md)
- [詳細仕様](docs/specification.md)
