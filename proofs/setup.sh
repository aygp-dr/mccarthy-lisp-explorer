#!/bin/sh
# Create proofs directory structure within the McCarthy Lisp Explorer project
mkdir -p ./proofs/basic
mkdir -p ./proofs/factorial
mkdir -p ./proofs/gcd
mkdir -p ./proofs/fibonacci
mkdir -p ./proofs/sqrt
mkdir -p ./proofs/lambda

# Create _CoqProject file
cat > ./proofs/_CoqProject << EOF
-R . McCarthyLispProofs
EOF

echo "Directory structure created successfully!"
echo "To compile all proofs, navigate to ./proofs and run:"
echo "coq_makefile -f _CoqProject *.v **/*.v -o Makefile && make"
