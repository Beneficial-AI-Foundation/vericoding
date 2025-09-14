// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 4): implemented recursively to avoid compiler index check limitations */
function AddRows(rowA: seq<int>, rowB: seq<int>): (result: seq<int>)
  requires |rowA| == |rowB|
  ensures |result| == |rowA|
  ensures forall j :: 0 <= j < |result| ==> result[j] == rowA[j] + rowB[j]
  decreases |rowA|
{
  if |rowA| == 0 then []
  else [rowA[0] + rowB[0]] + AddRows(rowA[1..], rowB[1..])
}
// </vc-helpers>

// <vc-spec>
method IndexWiseAddition(a: seq<seq<int>>, b: seq<seq<int>>) returns (result: seq<seq<int>>)
    requires |a| > 0 && |b| > 0
    requires |a| == |b|
    requires forall i :: 0 <= i < |a| ==> |a[i]| == |b[i]|
    ensures |result| == |a|
    ensures forall i :: 0 <= i < |result| ==> |result[i]| == |a[i]|
    ensures forall i :: 0 <= i < |result| ==> forall j :: 0 <= j < |result[i]| ==> result[i][j] == a[i][j] + b[i][j]
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 4): used a while loop to avoid compiler index check limitations */
  result := [];
  var i := 0;
  while i < |a|
    invariant |result| == i
    invariant i <= |a|
    invariant forall k :: 0 <= k < i ==> result[k] == AddRows(a[k], b[k])
  {
    var addedRow := AddRows(a[i], b[i]);
    result := result + [addedRow];
    i := i + 1;
  }
}
// </vc-code>
