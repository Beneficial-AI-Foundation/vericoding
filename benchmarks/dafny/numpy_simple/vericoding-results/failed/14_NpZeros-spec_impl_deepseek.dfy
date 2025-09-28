// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Fixed syntax - methods should be functions */
function createZeros1D(n: nat): array<int>
    ensures 
        result.Length == n &&
        (forall i :: 0 <= i < n ==> result[i] == 0)
{
    var arr := new int[n];
    var i := 0;
    while i < n
        invariant 0 <= i <= n
        invariant forall j :: 0 <= j < i ==> arr[j] == 0
    {
        arr[i] := 0;
        i := i + 1;
    }
    arr
}

function createZeros2D(rows: nat, cols: nat): array<array<int>>
    ensures 
        result.Length == rows &&
        (forall i :: 0 <= i < rows ==> result[i].Length == cols) &&
        (forall i, j :: 0 <= i < rows && 0 <= j < cols ==> result[i][j] == 0)
{
    var arr := new array<array<int>>[rows];
    var i := 0;
    while i < rows
        invariant 0 <= i <= rows
        invariant forall k :: 0 <= k < i ==> arr[k] != null
        invariant forall k :: 0 <= k < i ==> arr[k].Length == cols
        invariant forall k, j :: 0 <= k < i && 0 <= j < cols ==> arr[k][j] == 0
    {
        var row := new int[cols];
        var j := 0;
        while j < cols
            invariant 0 <= j <= cols
            invariant forall l :: 0 <= l < j ==> row[l] == 0
        {
            row[j] := 0;
            j := j + 1;
        }
        arr[i] := row;
        i := i + 1;
    }
    arr
}
// </vc-helpers>

// <vc-spec>
method zeros(n: nat) returns (result: array<int>)
    ensures 
        result.Length == n &&
        (forall i :: 0 <= i < n ==> result[i] == 0)
{
    assume {:axiom} false;
}

method zeros2d(rows: nat, cols: nat) returns (result: array<array<int>>)
    ensures 
        result.Length == rows &&
        (forall i :: 0 <= i < rows ==> result[i].Length == cols) &&
        (forall i, j :: 0 <= i < rows && 0 <= j < cols ==> result[i][j] == 0)
{
    assume {:axiom} false;
}
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 5): Fixed method call syntax */
  result := createZeros1D(n);
}
// </vc-code>
