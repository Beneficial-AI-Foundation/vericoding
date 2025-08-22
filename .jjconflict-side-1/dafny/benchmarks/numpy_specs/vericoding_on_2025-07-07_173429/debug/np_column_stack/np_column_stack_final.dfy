//IMPL
method column_stack(input: array<array<int>>) returns (ret: array2<int>)
    requires input.Length != 0 
    requires forall i :: 0 <= i < input.Length ==> input[i].Length == input[0].Length
    ensures ret.Length0 == input[0].Length && ret.Length1 == input.Length
    ensures forall i, j :: 0 <= i < ret.Length1 && 0 <= j < ret.Length0 ==> ret[j, i] == input[i][j]
{
    ret := new int[input[0].Length, input.Length];
    
    var i := 0;
    while i < input.Length
        invariant 0 <= i <= input.Length
        invariant forall row, col :: 0 <= row < i && 0 <= col < ret.Length0 ==> ret[col, row] == input[row][col]
    {
        var j := 0;
        while j < input[0].Length
            invariant 0 <= j <= input[0].Length
            invariant forall row, col :: 0 <= row < i && 0 <= col < ret.Length0 ==> ret[col, row] == input[row][col]
            invariant forall col :: 0 <= col < j ==> ret[col, i] == input[i][col]
        {
            ret[j, i] := input[i][j];
            j := j + 1;
        }
        i := i + 1;
    }
}