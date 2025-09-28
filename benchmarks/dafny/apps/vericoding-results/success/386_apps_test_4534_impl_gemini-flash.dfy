// <vc-preamble>
function binomial(n: int, k: int): int
    requires 0 <= k <= n
{
    if k == 0 || k == n then 1
    else if k == 1 then n
    else binomial(n-1, k-1) + binomial(n-1, k)
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): no change needed for this iteration */
predicate IsPascalRow(k: int, row: seq<int>)
    requires 0 <= k
{
    |row| == k + 1 &&
    (forall i :: 0 <= i < |row| ==> row[i] == binomial(k, i))
}
// </vc-helpers>

// <vc-spec>
method getRow(k: int) returns (result: seq<int>)
    requires 0 <= k <= 33
    ensures |result| == k + 1
    ensures forall i :: 0 <= i < |result| ==> result[i] == binomial(k, i)
    ensures forall i :: 0 <= i < |result| ==> result[i] > 0
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 2): changed array to sequence to fix type mismatch */
{
  var row := new int[k + 1];
  if k == 0 {
    row[0] := 1;
    return [1];
  } else {
    var prevRow := getRow(k - 1);
    var newRow: seq<int> := [1];
    var i := 1;
    while i < k
      invariant 0 <= i <= k
      invariant |newRow| == i
      invariant forall j :: 0 <= j < |newRow| ==> newRow[j] == binomial(k, j)
      invariant forall j :: 0 <= j < |prevRow| ==> prevRow[j] == binomial(k - 1, j)
    {
      newRow := newRow + [prevRow[i - 1] + prevRow[i]];
      i := i + 1;
    }
    newRow := newRow + [1];
    return newRow;
  }
}
// </vc-code>
