

// <vc-helpers>
function HelperNumberToName(n: int): string
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

method HelperSortSeq(s: seq<int>) returns (sorted: seq<int>)
  ensures forall i, j :: 0 <= i < j < |sorted| ==> sorted[i] <= sorted[j]
  ensures |sorted| == |s|
  ensures multiset(s) == multiset(sorted)
  decreases |s|
{
  if |s| == 0 {
    return [];
  } else if |s| == 1 {
    return s;
  } else {
    var min := s[0];
    var minIndex := 0;
    var i := 1;
    while i < |s|
      invariant min == s[minIndex]
      invariant 0 <= minIndex < i
      invariant min in s[0..i]
      invariant forall j :: 0 <= j < i ==> min <= s[j]
    {
      if s[i] < min {
        min := s[i];
        minIndex := i;
      }
      i := i + 1;
    }
    var s' := s[0..minIndex] + s[minIndex+1..];
    var sorted' := HelperSortSeq(s');
    return [min] + sorted';
  }
}

method HelperReverse(s: seq<int>) returns (rev: seq<int>)
  ensures |rev| == |s|
  ensures forall k :: 0 <= k < |s| ==> rev[k] == s[|s|-1-k]
{
  rev := seq(|s|, i requires 0<=i<|s| => s[|s|-1-i]);
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
  var sortedArr := HelperSortSeq(arr);
  var revArr := HelperReverse(sortedArr);
  result := [];
  var index := 0;
  while index < |revArr|
    invariant 0 <= index <= |revArr|
    invariant |result| == index
    invariant forall i :: 0 <= i < |result| ==>
               result[i] in ["One", "Two", "Three", "Four", "Five", "Six", "Seven", "Eight", "Nine"]
  {
    var x := revArr[index];
    if 1 <= x <= 9 {
      result := result + [HelperNumberToName(x)];
    }
    index := index + 1;
  }
  return result;
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