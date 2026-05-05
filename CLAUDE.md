# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

## Overview

Lean 4 の学習・練習用リポジトリ。定理証明と関数型プログラミングの習得を目的としている。

## Setup

Lean 4 のインストールは [elan](https://github.com/leanprover/elan)（Lean のバージョンマネージャ）経由で行う。

```bash
curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh
```

`elan` が入っていれば、`lean-toolchain` ファイルが存在するディレクトリで `lake` を実行すると自動的に適切なバージョンが取得される。

## Build System: Lake

Lean 4 のビルドツールは [Lake](https://github.com/leanprover/lake)。プロジェクトは `lakefile.lean`（または `lakefile.toml`）で定義する。

```bash
lake build          # プロジェクト全体をビルド
lake build Target   # 特定ターゲットのみビルド
lake clean          # ビルド成果物を削除
lake exe <name>     # 実行ファイルを起動
```

## Checking Individual Files

単一ファイルの型検査・証明チェック：

```bash
lean SomeFile.lean
```

## Project Structure

```
src/
  02/natural-number.lean   # 自然数の帰納的定義・加算の実装と証明
  03/prop-logic.lean       # 命題論理（三段論法・対偶・爆発律・同値性）
```

章番号のディレクトリ以下に `.lean` ファイルを置く構成。新しい章は `src/<番号>/` に追加していく。

## ファイル追加時のワークフロー

「（ファイル名）を追加して」と言われたら：

0. ファイルを特定する `src/<番号>/<ファイル名>.lean`
1. そのファイルの内容を読んで把握する
2. `README.md` の **末尾に** エントリを追加する（`- \`パス\` — 内容の一行説明` 形式）
3. `/git commit` で変更をコミットする

`/add (ファイル名)` コマンドはこのワークフローを自動化するためのショートカット

## Lean 4 Notes

- `#check`, `#eval`, `#reduce` はインライン確認用コマンド（`#reduce` は正規化して出力）
- `sorry` はひとまず証明を通過させるプレースホルダ（残さない）
- タクティクは `by` ブロック内で使う：`exact`, `apply`, `intro`, `constructor`, `simp`, `trivial`, `contradiction`, `exfalso` など
- Mathlib を使う場合は `lakefile.lean` に依存を追加し `import Mathlib` で利用可能
