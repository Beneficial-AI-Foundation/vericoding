

// <vc-helpers>
method SortSeq(s: seq<int>) returns (sorted: seq<int>)
  ensures forall i, j :: 0 <= i < j < |sorted| ==> sorted[i] <= sorted[j]
  ensures |sorted| == |s|
  ensures multiset(s) == multiset(sorted)
{
  if |s| <= 1 {
    sorted := s;
  } else {
    var mid := |s| / 2;
    var left := SortSeq(s[0..mid]);
    var right := SortSeq(s[mid..]);
    sorted := Merge(left, right);
  }
}

method Merge(left: seq<int>, right: seq<int>) returns (merged: seq<int>)
  requires |left| == 0 || forall i, j :: 0 <= i < j < |left| ==> left[i] <= left[j]
  requires |right| == 0 || forall i, j :: 0 <= i < j < |right| ==> right[i] <= right[j]
  ensures |merged| == |left| + |right|
  ensures multiset(merged) == multiset(left) + multiset(right)
  ensures |merged| == 0 || forall i, j :: 0 <= i < j < |merged| ==> merged[i] <= merged[j]
{
  if |left| == 0 {
    merged := right;
  } else if |right| == 0 {
    merged := left;
  } else if left[0] <= right[0] {
    var rest := Merge(left[1..], right);
    merged := [left[0]] + rest;
  } else {
    var rest := Merge(left, right[1..]);
    merged := [right[0]] + rest;
  }
}

method reverse(s: seq<int>) returns (rev: seq<int>)
  ensures |rev| == |s|
  ensures forall k :: 0 <= k < |s| ==> rev[k] == s[|s| - 1 - k]
{
  rev := [];
  var i := 0;
  while i < |s|
    invariant |rev| == i
    invariant forall k :: 0 <= k < i ==> rev[k] == s[|s| - 1 - k]
  {
    rev := rev + [s[|s| - 1 - i]];
    i := i + 1;
  }
}
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
  result := [];
  var i := 0;
  
  while i < |reversed|
    invariant i <= |reversed|
    invariant |result| == i
    invariant forall j :: 0 <= j < i ==> result[j] in ["One", "Two", "Three", "Four", "Five", "Six", "Seven", "Eight", "Nine"]
  {
    if reversed[i] >= 1 && reversed[i] <= 9 {
      result := result + [NumberToName(reversed[i])];
    }
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