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

// <vc-description>
/*
function_signature: method reverse(s: seq<int>) returns (rev: seq<int>)
Reverse order. Ensures: returns the correct size/count; the condition holds for all values.
*/
// </vc-description>

// <vc-spec>
method reverse(s: seq<int>) returns (rev: seq<int>)
  ensures |rev| == |s|
  ensures forall i :: 0 <= i < |s| ==> rev[i] == s[|s| - 1 - i]
// </vc-spec>
// <vc-code>
{
  rev := [];
  var i := |s|;
  while i > 0
    invariant 0 <= i <= |s|
    invariant |rev| == |s| - i
    invariant forall j :: 0 <= j < |rev| ==> rev[j] == s[|s| - 1 - j]
  {
    i := i - 1;
    rev := rev + [s[i]];
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