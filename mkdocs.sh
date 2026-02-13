#!/bin/bash
cd docbuild
lake build LeanStudy:docs
cd ..
rm -r docs
cp -pr docbuild/.lake/build/doc docs
touch docs/.nojekyll

