predicate ValidInput(a: seq<int>)
{
    |a| > 0
}

predicate isSorted(x: seq<int>)
{
    forall i, j :: 0 <= i < j < |x| ==> x[i] <= x[j]
}

function thanosSort(x: seq<int>): int
    requires |x| > 0
    ensures thanosSort(x) >= 1
    ensures thanosSort(x) <= |x|
    ensures isSorted(x) ==> thanosSort(x) == |x|
{
    var len := |x|;
    if isSorted(x) then
        len
    else
        var firstHalf := x[..len/2];
        var secondHalf := x[len/2..];
        var leftResult := thanosSort(firstHalf);
        var rightResult := thanosSort(secondHalf);
        if leftResult > rightResult then leftResult else rightResult
}

// <vc-helpers>
function thanosSort(x: seq<int>): int
  requires |x| > 0
  ensures thanosSort(x) >= 1
  ensures thanosSort(x) <= |x|
  ensures isSorted(x) ==> thanosSort(x) == |x|
  decreases |x|
{
  var len := |x|;
  if isSorted(x) then
    len
  else
    var firstHalf := x[..len/2];
    var secondHalf := x[len/2..];
    var leftResult := thanosSort(firstHalf);
    var rightResult := thanosSort(secondHalf);
    if leftResult > rightResult then leftResult else rightResult
}
// </vc-helpers>

// <vc-spec>
method solve(a: seq<int>) returns (result: int)
    requires ValidInput(a)
    ensures result == thanosSort(a)
    ensures 1 <= result <= |a|
// </vc-spec>
// <vc-code>
{
  decreases |a|;
  var len := |a|;
  if isSorted(a) then
    result := len;
  else
    var firstHalf := a[..len/2];
    var secondHalf := a[len/2..];
    var leftResult := solve(firstHalf);
    var rightResult := solve(secondHalf);
    result := if leftResult > rightResult then leftResult else rightResult;
}
// </vc-code>

