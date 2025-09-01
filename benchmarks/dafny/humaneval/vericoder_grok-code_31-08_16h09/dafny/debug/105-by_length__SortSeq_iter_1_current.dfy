method SortReverseAndName(arr: seq<int>) returns (result: seq<string>)
  // post-conditions-start
  ensures |result| <= |arr|
  ensures forall i :: 0 <= i < |result| ==>
    result[i] in ["One", "Two", "Three", "Four", "Five", "Six", "Seven", "Eight", "Nine"]
  // post-conditions-end
{
  assume{:axiom} false;
}

// <vc-helpers>
function insert(sorted: seq<int>, x: int): seq<int>
  requires forall i,j :: 0 <= i < j < |sorted| ==> sorted[i] <= sorted[j]
  ensures forall i,j :: 0 <= i < j < |insert| ==> insert[i] <= insert[j]
  ensures |insert| == |sorted| + 1
  ensures multiset(insert) == multiset(sorted + [x])
{
  if |sorted| == 0 then [x]
  else if x <= sorted[0] then [x] + sorted
  else [sorted[0]] + insert(sorted[1..], x)
}
// </vc-helpers>

// <vc-spec>
method SortSeq(s: seq<int>) returns (sorted: seq<int>)
  // post-conditions-start
  ensures forall i, j :: 0 <= i < j < |sorted| ==> sorted[i] <= sorted[j]
  ensures |sorted| == |s|
  ensures multiset(s) == multiset(sorted)
  // post-conditions-end
// </vc-spec>
// <vc-code>
{
  var sorted := [];
  var i := 0;
  while i < |s|
    invariant 0 <= i <= |s|
    invariant |sorted| == i
    invariant forall j,k :: 0 <= j < k < |sorted| ==> sorted[j] <= sorted[k]
    invariant multiset(sorted) == multiset(s[..i])
  {
    sorted := insert(sorted, s[i]);
    i := i + 1;
  }
}
// </vc-code>

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