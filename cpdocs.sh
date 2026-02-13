#!/bin/bash
rm -r docs
cp -pr docbuild/.lake/build/doc docs
touch docs/.nojekyll

