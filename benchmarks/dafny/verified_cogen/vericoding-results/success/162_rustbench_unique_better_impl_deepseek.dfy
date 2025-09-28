// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
function sortedSubsequence(a: array<int>): (r: seq<int>)
  reads a
  ensures forall i, j | 0 <= i < j < |r| :: r[i] < r[j]
  ensures forall x | x in r :: x in a[..]
{
  if a.Length == 0 then
    []
  else
    sortedSubsequenceRec(a, 0)
}

function sortedSubsequenceRec(a: array<int>, i: int): (r: seq<int>)
  requires 0 <= i <= a.Length
  reads a
  decreases a.Length - i
  ensures forall k, l | 0 <= k < l < |r| :: r[k] < r[l]
  ensures forall x | x in r :: x in a[i..]
{
  if i == a.Length then
    []
  else if i == a.Length - 1 then
    [a[i]]
  else
    var rest := sortedSubsequenceRec(a, i+1);
    if |rest| == 0 || a[i] < rest[0] then
      [a[i]] + rest
    else
      rest
}
// </vc-helpers>

// <vc-spec>
method UniqueBetter(a: array<int>) returns (result: seq<int>)
    requires
        forall i: int, j: int ::
            0 <= i && i < j && j < a.Length ==> a[i] <= a[j]
    ensures
        forall i: int, j: int ::
            0 <= i && i < j && j < |result| ==> result[i] < result[j]
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 2): Add proper result assignment */
{
  result := sortedSubsequence(a);
}
// </vc-code>
