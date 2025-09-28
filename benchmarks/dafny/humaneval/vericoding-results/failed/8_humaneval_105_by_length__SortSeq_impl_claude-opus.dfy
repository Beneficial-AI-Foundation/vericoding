// <vc-preamble>
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
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): Fixed InsertSorted to correctly maintain multiset property */
function IsSorted(s: seq<int>): bool
{
  forall i, j :: 0 <= i < j < |s| ==> s[i] <= s[j]
}

method InsertSorted(sorted: seq<int>, x: int) returns (result: seq<int>)
  requires IsSorted(sorted)
  ensures IsSorted(result)
  ensures |result| == |sorted| + 1
  ensures multiset(result) == multiset(sorted) + multiset{x}
{
  if |sorted| == 0 {
    result := [x];
  } else {
    var i := 0;
    while i < |sorted| && sorted[i] <= x
      invariant 0 <= i <= |sorted|
      invariant forall j :: 0 <= j < i ==> sorted[j] <= x
    {
      i := i + 1;
    }
    result := sorted[..i] + [x] + sorted[i..];
    assert result == sorted[..i] + [x] + sorted[i..];
    assert multiset(result) == multiset(sorted[..i]) + multiset{x} + multiset(sorted[i..]);
    assert multiset(sorted[..i]) + multiset(sorted[i..]) == multiset(sorted);
  }
}
// </vc-helpers>

// <vc-spec>
method SortSeq(s: seq<int>) returns (sorted: seq<int>)

  ensures forall i, j :: 0 <= i < j < |sorted| ==> sorted[i] <= sorted[j]
  ensures |sorted| == |s|
  ensures multiset(s) == multiset(sorted)
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 2): Fixed loop to correctly call InsertSorted and maintain invariants */
  sorted := [];
  var i := 0;
  while i < |s|
    invariant 0 <= i <= |s|
    invariant IsSorted(sorted)
    invariant |sorted| == i
    invariant multiset(sorted) == multiset(s[..i])
  {
    var newSorted := InsertSorted(sorted, s[i]);
    sorted := newSorted;
    assert multiset(sorted) == multiset(s[..i]) + multiset{s[i]};
    assert s[..i+1] == s[..i] + [s[i]];
    assert multiset(s[..i+1]) == multiset(s[..i]) + multiset{s[i]};
    i := i + 1;
  }
  assert i == |s|;
  assert s[..i] == s;
}
// </vc-code>
