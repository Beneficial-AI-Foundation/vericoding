

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method SortReverseAndName(arr: seq<int>) returns (result: seq<string>)
  // post-conditions-start
  ensures |result| <= |arr|
  ensures forall i :: 0 <= i < |result| ==>
    result[i] in ["One", "Two", "Three", "Four", "Five", "Six", "Seven", "Eight", "Nine"]
  // post-conditions-end
// </vc-spec>
// <vc-code>
{
  var sorted := SortSeq(arr);
  var reversed := reverse(sorted);
  
  var filtered := [];
  var i := 0;
  while i < |reversed|
    invariant 0 <= i <= |reversed|
    invariant |filtered| <= i
    invariant forall j :: 0 <= j < |filtered| ==> 1 <= filtered[j] <= 9
  {
    if 1 <= reversed[i] <= 9 {
      filtered := filtered + [reversed[i]];
    }
    i := i + 1;
  }
  
  result := [];
  i := 0;
  while i < |filtered|
    invariant 0 <= i <= |filtered|
    invariant |result| == i
    invariant forall j :: 0 <= j < |result| ==>
      result[j] in ["One", "Two", "Three", "Four", "Five", "Six", "Seven", "Eight", "Nine"]
    invariant forall j :: 0 <= j < |filtered| ==> 1 <= filtered[j] <= 9
  {
    result := result + [NumberToName(filtered[i])];
    i := i + 1;
  }
}
// </vc-code>

method SortSeq(s: seq<int>) returns (sorted: seq<int>)
  // post-conditions-start
  ensures forall i, j :: 0 <= i < j < |sorted| ==> sorted[i] <= sorted[j]
  ensures |sorted| == |s|
  ensures multiset(s) == multiset(sorted)
  // post-conditions-end
{
  assume{:axiom} false;
}
method reverse(s: seq<int>) returns (rev: seq<int>)
  // post-conditions-start
  ensures |rev| == |s|
  ensures forall k :: 0 <= k < |s| ==> rev[k] == s[|s| - 1 - k]
  // post-conditions-end
{
  assume{:axiom} false;
}
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