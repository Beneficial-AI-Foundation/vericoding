

// <vc-helpers>
method SortSeq(s: seq<int>) returns (sorted: seq<int>)
  ensures forall i, j :: 0 <= i < j < |sorted| ==> sorted[i] <= sorted[j]
  ensures |sorted| == |s|
  ensures multiset(s) == multiset(sorted)
{
  if |s| == 0 {
    sorted := [];
  } else {
    var recSorted := SortSeq(s[..|s|-1]);
    var x := s[|s|-1];
    sorted := [];
    var inserted := false;
    var i := 0;
    while i < |recSorted| && !inserted
      invariant 0 <= i <= |recSorted|
      invariant forall k, l :: 0 <= k < l < |sorted| ==> sorted[k] <= sorted[l]
      invariant multiset(sorted) + multiset(recSorted[i..]) + multiset([x]) == multiset(s)
      invariant |sorted| + |recSorted[i..]| == |recSorted|
    {
      if x <= recSorted[i] {
        sorted := sorted + [x] + recSorted[i..];
        inserted := true;
      } else {
        sorted := sorted + [recSorted[i]];
        i := i + 1;
      }
    }
    if !inserted {
      sorted := sorted + [x];
    }
  }
}

method reverse(s: seq<int>) returns (rev: seq<int>)
  ensures |rev| == |s|
  ensures forall k :: 0 <= k < |s| ==> rev[k] == s[|s| - 1 - k]
{
  rev := [];
  var i := |s| - 1;
  while i >= 0
    invariant -1 <= i <= |s| - 1
    invariant |rev| == |s| - 1 - i
  {
    rev := rev + [s[i]];
    i := i - 1;
  }
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
  var tempResult: seq<int> := [];
  var i := 0;
  while i < |arr| {
    var x := arr[i];
    if 1 <= x <= 9 {
      tempResult := tempResult + [x];
    }
    i := i + 1;
  }
  var sorted := SortSeq(tempResult);
  var reversed := reverse(sorted);
  result := [];
  var j := 0;
  while j < |reversed| {
    var y := reversed[j];
    result := result + [NumberToName(y)];
    j := j + 1;
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