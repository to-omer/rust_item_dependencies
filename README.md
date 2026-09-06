# rust-item-dependencies

`rust-item-dependencies`は、1ファイルのRustプログラムから実行に不要なコードを取り除くツールです。名前解決、型の選択、マクロ展開など、コンパイラが確定した依存関係をもとに残すコードを判断します。

## 使い方

リポジトリのルートで、削減したいファイルを指定します。

```console
cargo rid input.rs
```

`input.rs`を削減し、検証に成功した結果で同じファイルを更新します。別のファイルへ保存する場合は`-o reduced.rs`を追加します。初回だけ専用のRustコンパイラを`target/`配下に用意するため、完了まで時間がかかります。

## ドキュメント

- [利用ガイド](docs/README.md)
- [詳細仕様](docs/specification.md)
