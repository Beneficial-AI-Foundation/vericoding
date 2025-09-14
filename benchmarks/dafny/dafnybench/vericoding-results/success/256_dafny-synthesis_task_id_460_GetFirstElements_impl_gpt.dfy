

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method GetFirstElements(lst: seq<seq<int>>) returns (result: seq<int>)
    requires forall i :: 0 <= i < |lst| ==> |lst[i]| > 0
    ensures |result| == |lst|
    ensures forall i :: 0 <= i < |result| ==> result[i] == lst[i][0]
// </vc-spec>
// <vc-code>
{
  var res: seq<int> := [];
  var i := 0;
  while i < |lst|
    invariant 0 <= i <= |lst|
    invariant |res| == i
    invariant forall j :: 0 <= j < i ==> res[j] == lst[j][0]
  {
    assert |lst[i]| > 0;
    res := res + [lst[i][0]];
    i := i + 1;
  }
  return res;
}
// </vc-code>

