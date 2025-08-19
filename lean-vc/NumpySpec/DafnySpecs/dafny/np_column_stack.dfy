//https://numpy.org/doc/stable/reference/generated/numpy.column_stack.html#numpy.column_stack
//Stack 1-D arrays as columns into a 2-D array.

method column_stack(input: array<array<int>>) returns (ret: array2<int>)
    requires input.Length != 0; 
    requires forall i :: 0 <= i < input.Length ==> input[i].Length == input[0].Length;
    ensures ret.Length0 == input[0].Length && ret.Length1 == input.Length;
    ensures forall i, j :: 0 <= i < ret.Length1 && 0 <= j < ret.Length0 ==> ret[j, i] == input[i][j];
{}