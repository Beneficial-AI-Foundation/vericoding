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
lemma ReversePreservesLength(s: seq<int>)
  ensures |reverse(s)| == |s|
{
  calc {
    |reverse(s)| == |s| { assert reverse(s)[k] == s[|s|-1-k] forall k; }
  }
}

lemma ReversePreservesMultiset(s: seq<int>)
  ensures multiset(reverse(s)) == multiset(s)
{
  calc {
    multiset(reverse(s))
    == multiset(s[k | k in 0..|s| :: s[|s|-1-k]])
    { assert multiset(s) == multiset(s[k | k in 0..|s| :: s[k]]); }
    == multiset(s)
  }
}

lemma SortedAndReversedAreEqual(s: seq<int>)
  requires forall i, j :: 0 <= i < j < |s| ==> s[i] <= s[j]
  requires forall i, j :: 0 <= i < j < |s| ==> reverse(s)[i] <= reverse(s)[j]
  ensures s == reverse(s)
{
  assert |s| == |reverse(s)|;
  if |s| > 0 {
    assert s[0] <= s[|s|-1];
    assert reverse(s)[0] == s[|s|-1];
    assert reverse(s)[|s|-1] == s[0];
    assert s[|s|-1] <= s[0];
    assert s[0] == s[|s|-1];
    var s' := s[1..|s|-1];
    var rev_s' := reverse(s');
    assert reverse(s)[1..|s|-1] == rev_s';
    assert s' == rev_s';
    assert s[1..|s|-1] == reverse(s')[1..|s|-1];
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
  var sorted := SortSeq(arr);
  var reversed := reverse(sorted);
  var filtered := [i | i in reversed :: 1 <= i <= 9];
  result := seq(|filtered|, i requires 0 <= i < |filtered| => NumberToName(filtered[i]));
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