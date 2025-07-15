#\!/bin/bash

# Function to convert underscore_case to PascalCase
to_pascal_case() {
    echo "$1" | sed 's/_\(.\)/\U\1/g' | sed 's/^\(.\)/\U\1/'
}

# Create ArrayManipulation.lean
cat > lean-vc/benchmarks/numpy_specs/hoare_triple/ArrayManipulation.lean << 'EOL'
/-\!
# Array Manipulation Specifications

Import all array manipulation function specifications.
-/

EOL
find lean-vc/benchmarks/numpy_specs/hoare_triple/array_manipulation -name "*.lean" | sort | sed 's|lean-vc/||' | sed 's|\.lean$||' | sed 's|/|.|g' | sed 's|^|import |' >> lean-vc/benchmarks/numpy_specs/hoare_triple/ArrayManipulation.lean

# Create BitwiseOperations.lean
cat > lean-vc/benchmarks/numpy_specs/hoare_triple/BitwiseOperations.lean << 'EOL'
/-\!
# Bitwise Operations Specifications

Import all bitwise operations function specifications.
-/

EOL
find lean-vc/benchmarks/numpy_specs/hoare_triple/bitwise_operations -name "*.lean" | sort | sed 's|lean-vc/||' | sed 's|\.lean$||' | sed 's|/|.|g' | sed 's|^|import |' >> lean-vc/benchmarks/numpy_specs/hoare_triple/BitwiseOperations.lean

# Continue for all categories...
for dir in constants data_type_routines datetime_support fft indexing_slicing io_operations linalg logic_functions mathematical_functions ndarray polynomial random set_operations sorting_searching statistics strings testing typing ufunc ufuncs; do
    pascal_name=$(to_pascal_case "$dir")
    cat > "lean-vc/benchmarks/numpy_specs/hoare_triple/${pascal_name}.lean" << EOL
/-\!
# ${pascal_name} Specifications

Import all ${dir} function specifications.
-/

EOL
    find "lean-vc/benchmarks/numpy_specs/hoare_triple/${dir}" -name "*.lean" 2>/dev/null | sort | sed 's|lean-vc/||' | sed 's|\.lean$||' | sed 's|/|.|g' | sed 's|^|import |' >> "lean-vc/benchmarks/numpy_specs/hoare_triple/${pascal_name}.lean"
done
