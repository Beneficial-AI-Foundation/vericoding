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
// Implementation of reverse using an explicit loop for clarity and verification.
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
  var accum: seq<int> := [];
  for i := |s| - 1 downto 0
    invariant |accum| == |s| - i - 1
    invariant forall j :: 0 <= j < |accum| ==> accum[j] == s[|s| - j - 1]
  {
    accum := accum + [s[i]];
  }
  rev := accum;
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