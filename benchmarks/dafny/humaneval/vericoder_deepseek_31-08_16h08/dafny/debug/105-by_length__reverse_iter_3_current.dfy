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
lemma ReverseLemma(s: seq<int>, k: int)
  requires 0 <= k < |s|
  ensures |s| - 1 - k >= 0
  ensures |s| - 1 - k < |s|
{
}

lemma ReversePreservesLength(s: seq<int>, rev: seq<int>)
  requires |rev| == |s|
  ensures |rev| == |s|
{
}

lemma ReverseIndexLemma(s: seq<int>, rev: seq<int>, i: int)
  requires |rev| == |s| - i - 1
  requires forall k :: i + 1 <= k < |s| ==> rev[k - i - 1] == s[k]
  requires i >= -1
  requires -1 <= i < |s|
  ensures forall k :: 0 <= k < |rev| ==> rev[k] == s[|s| - |rev| + k]
{
}
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
  rev := [];
  var i := |s| - 1;
  while i >= 0
    invariant -1 <= i < |s|
    invariant |rev| == |s| - i - 1
    invariant forall k :: i + 1 <= k < |s| ==> rev[k - i - 1] == s[k]
  {
    rev := [s[i]] + rev;
    i := i - 1;
  }
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