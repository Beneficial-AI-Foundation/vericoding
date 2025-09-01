method SortReverseAndName(arr: seq<int>) returns (result: seq<string>)
  // post-conditions-start
  ensures |result| <= |arr|
  ensures forall i :: 0 <= i < |result| ==>
    result[i] in ["One", "Two", "Three", "Four", "Five", "Six", "Seven", "Eight", "Nine"]
  // post-conditions-end
{
  assume{:axiom} false;
}
method SortSeq(s: seq<int>) returns (sorted: seq<int>)
  // post-conditions-start
  ensures forall i, j :: 0 <= i < j < |sorted| ==> sorted[i] <= sorted[j]
  ensures |sorted| == |s|
  ensures multiset(s) == multiset(sorted)
  // post-conditions-end
{
  assume{:axiom} false;
}

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method reverse(s: seq<int>) returns (rev: seq<int>)
  // post-conditions-start
  ensures |rev| == |s|
  ensures forall k :: 0 <= k < |s| ==> rev[k] == s[|s| - 1 - k]
  // post-conditions-end
// </vc-spec>
// <vc-code>
{
  var i := |s|;
  rev := [];
  while i > 0
    invariant 0 <= i <= |s|
    invariant |rev| == |s| - i
    invariant forall k :: 0 <= k < |rev| ==> rev[k] == s[|s| - 1 - k]
    decreases i
  {
    var oldRev := rev;
    var oldI := i;
    i := i - 1;
    rev := oldRev + [s[i]];

    assert oldI == i + 1;
    assert |oldRev| == |s| - oldI;
    assert |rev| == |oldRev| + 1;
    assert |rev| == |s| - i;

    forall k | 0 <= k < |rev|
      ensures rev[k] == s[|s| - 1 - k]
    {
      if k < |oldRev| {
        assert rev[k] == oldRev[k];
        assert oldRev[k] == s[|s| - 1 - k];
      } else {
        assert k < |oldRev| + 1;
        assert k >= |oldRev|;
        assert k == |oldRev|;
        assert rev[k] == s[i];
        assert |oldRev| == |s| - oldI;
        assert oldI == i + 1;
        assert |s| - 1 - k == i;
      }
    }
  }
  assert i == 0;
}
// </vc-code>

function NumberToName(n: int): string
  requires 1 <= n <= 9
{
  match n
  case 1 => "One"
  case 2 => "Two"
  case 3 => "Three"
  case 4 => "Four"
  case 5 => "Five"
  case 6 => "Six"
  case 7 => "Seven"
  case 8 => "Eight"
  case 9 => "Nine"
}
// pure-end