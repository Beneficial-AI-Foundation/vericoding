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
lemma SortedPreservesElements(s: seq<int>, sorted: seq<int>)
  requires forall i, j :: 0 <= i < j < |sorted| ==> sorted[i] <= sorted[j]
  requires |sorted| == |s|
  requires multiset(s) == multiset(sorted)
  ensures forall x :: x in s <==> x in sorted

function InsertSorted(x: int, sorted: seq<int>): seq<int>
  requires forall i, j :: 0 <= i < j < |sorted| ==> sorted[i] <= sorted[j]
  ensures forall i, j :: 0 <= i < j < |InsertSorted(x, sorted)| ==> InsertSorted(x, sorted)[i] <= InsertSorted(x, sorted)[j]
  ensures |InsertSorted(x, sorted)| == |sorted| + 1
  ensures multiset(InsertSorted(x, sorted)) == multiset(sorted) + multiset([x])
{
  if |sorted| == 0 then [x]
  else if x <= sorted[0] then [x] + sorted
  else [sorted[0]] + InsertSorted(x, sorted[1..])
}

lemma InsertSortedCorrect(x: int, sorted: seq<int>)
  requires forall i, j :: 0 <= i < j < |sorted| ==> sorted[i] <= sorted[j]
  ensures forall i, j :: 0 <= i < j < |InsertSorted(x, sorted)| ==> InsertSorted(x, sorted)[i] <= InsertSorted(x, sorted)[j]
  ensures multiset(InsertSorted(x, sorted)) == multiset(sorted) + multiset([x])
{
  if |sorted| == 0 {
  } else if x <= sorted[0] {
  } else {
    InsertSortedCorrect(x, sorted[1..]);
  }
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
  if |s| == 0 {
    return [];
  }
  
  var result := [s[0]];
  var i := 1;
  
  while i < |s|
    invariant 1 <= i <= |s|
    invariant |result| == i
    invariant forall x, y :: 0 <= x < y < |result| ==> result[x] <= result[y]
    invariant multiset(result) == multiset(s[0..i])
  {
    InsertSortedCorrect(s[i], result);
    result := InsertSorted(s[i], result);
    i := i + 1;
  }
  
  return result;
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