// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): trivial helper lemma placeholder */
lemma TrivialHelperIteration5()
  ensures true
{
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
  /* code modified by LLM (iteration 5): allocate array of length n and set all entries to 0 */
  result := new int[n];
  var i: int := 0;
  while i < n
    invariant 0 <= i <= n
    invariant result != null && result.Length == n
    invariant forall k: int :: 0 <= k < i ==> result[k] == 0
  {
    result[i] := 0;
    i := i + 1;
  }
}

{
  /* code modified by LLM (iteration 5): allocate 2D array rows x cols and set all entries to 0 */
  result := new (array<int>)[rows];
  var i: int := 0;
  while i < rows
    invariant 0 <= i <= rows
    invariant result != null && result.Length == rows
    invariant forall r: int :: 0 <= r < i ==> result[r] != null && result[r].Length == cols &&
                                   (forall c: int :: 0 <= c < cols ==> result[r][c] == 0)
  {
    var row := new int[cols];
    var j: int := 0;
    while j < cols
      invariant 0 <= j <= cols
      invariant row != null && row.Length == cols
      invariant forall c: int :: 0 <= c < j ==> row[c] == 0
    {
      row[j] := 0;
      j := j + 1;
    }
    result[i] := row;
    i := i + 1;
  }
}
// </vc-code>
