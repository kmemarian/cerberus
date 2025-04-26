#!/usr/bin/env bash

# Dealing with GNU sed and BSD/Darwin sed incompatibility
if sed --version 2>&1 | grep -q 'GNU sed'; then
  sed -i "$@"
else
  sed -i '' "$@"
fi
