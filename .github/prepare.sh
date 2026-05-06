#!/bin/bash
set -e

mkdir -p src
cp .github/book.toml .github/*.md ./

# Copy custom theme assets (language switcher, etc.)
if [ -d ".github/theme" ]; then
  cp -r .github/theme ./
fi
