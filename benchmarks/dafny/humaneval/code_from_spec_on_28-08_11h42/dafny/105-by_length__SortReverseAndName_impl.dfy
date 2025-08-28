// <vc-helpers>
lemma NumberToNameInRange(n: int)
  requires 1 <= n <= 9
  ensures NumberToName(n) in ["One", "Two", "Three", "Four", "Five", "Six", "Seven", "Eight", "Nine"]
{
}

lemma FilterPreservesValidRange(s: seq<int>)
  ensures forall x :: x in s && 1 <= x <= 9 ==> 1 <= x <= 9
{
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
  var filtered := seq(x | x in reversed && 1 <= x <= 9);
  
  assert forall x :: x in filtered ==> 1 <= x <= 9;
  
  var namedResult := seq(|filtered|, i requires 0 <= i < |filtered| => NumberToName(filtered[i]));
  
  forall i | 0 <= i < |namedResult|
    ensures namedResult[i] in ["One", "Two", "Three", "Four", "Five", "Six", "Seven", "Eight", "Nine"]
  {
    NumberToNameInRange(filtered[i]);
  }
  
  return namedResult;
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