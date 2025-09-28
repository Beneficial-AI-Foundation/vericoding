// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): simple lemma about naturals */
lemma NatIncrease(n: nat)
  ensures n + 1 > n
{
  assert n + 1 > n;
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
  /* code modified by LLM (iteration 5): allocate 1D zero-initialized array */
  result := new int[n];
}

{
  /* code modified by LLM (iteration 5): allocate 2D zero-initialized array */
  result := new array<array<int>>(rows);
  var i := 0;
  while i < rows
    invariant 0 <= i <= rows
    invariant result.Length == rows
    invariant (forall k :: 0 <= k < i ==> result[k] != null && result[k].Length == cols && (forall j :: 0 <= j < cols ==> result[k][j] == 0))
  {
    var row := new int[cols];
    result[i] := row;
    i := i + 1;
  }
}

// </vc-code>
