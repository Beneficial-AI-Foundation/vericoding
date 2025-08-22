//https://numpy.org/doc/stable/reference/generated/numpy.column_stack.html#numpy.column_stack
//Stack 1-D arrays as columns into a 2-D array.

method column_stack(input: array<array<int>>) returns (ret: array2<int>)
    requires input.Length != 0; 
    requires forall i :: 0 <= i < input.Length ==> input[i].Length == input[0].Length;
    ensures ret.Length0 == input[0].Length && ret.Length1 == input.Length;
    ensures forall i, j :: 0 <= i < ret.Length1 && 0 <= j < ret.Length0 ==> ret[j, i] == input[i][j];
{
    ret := new int[input[0].Length, input.Length];
    
    var col := 0;
    while col < input.Length
        invariant 0 <= col <= input.Length
        invariant forall i, j :: 0 <= i < col && 0 <= j < ret.Length0 ==> ret[j, i] == input[i][j]
    {
        var row := 0;
        while row < input[0].Length
            invariant 0 <= row <= input[0].Length
            invariant forall i, j :: 0 <= i < col && 0 <= j < ret.Length0 ==> ret[j, i] == input[i][j]
            invariant forall j :: 0 <= j < row ==> ret[j, col] == input[col][j]
        {
            ret[row, col] := input[col][row];
            row := row + 1;
        }
        col := col + 1;
    }
}