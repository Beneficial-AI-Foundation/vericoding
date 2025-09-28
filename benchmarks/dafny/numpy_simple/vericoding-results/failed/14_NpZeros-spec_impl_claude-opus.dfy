// <vc-preamble>
// </vc-preamble>

// <vc-helpers>

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
  /* code modified by LLM (iteration 5): Fixed to provide only method body for zeros */
  result := new int[n];
  var i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant forall j :: 0 <= j < i ==> result[j] == 0
  {
    result[i] := 0;
    i := i + 1;
  }
}

method zeros2d(rows: nat, cols: nat) returns (result: array<array<int>>)
    ensures 
        result.Length == rows &&
        (forall i :: 0 <= i < rows ==> result[i].Length == cols) &&
        (forall i, j :: 0 <= i < rows && 0 <= j < cols ==> result[i][j] == 0)
{
  /* code modified by LLM (iteration 5): Fixed to provide only method body for zeros2d */
  result := new array<int>[rows];
  var i := 0;
  while i < rows
    invariant 0 <= i <= rows
    invariant forall k :: 0 <= k < i ==> result[k].Length == cols
    invariant forall k, j :: 0 <= k < i && 0 <= j < cols ==> result[k][j] == 0
  {
    result[i] := new int[cols];
    var j := 0;
    while j < cols
      invariant 0 <= j <= cols
      invariant forall k :: 0 <= k < j ==> result[i][k] == 0
    {
      result[i][j] := 0;
      j := j + 1;
    }
    i := i + 1;
  }
}
// </vc-code>
