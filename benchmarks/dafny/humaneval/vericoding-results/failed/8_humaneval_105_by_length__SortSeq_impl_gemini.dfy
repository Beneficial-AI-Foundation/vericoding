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
/* helper modified by LLM (iteration 5): added lemmas for multiset properties and a call in Insert */
lemma MultisetSplit<T>(s: seq<T>, i: int)
  requires 0 <= i <= |s|
  ensures multiset(s) == multiset(s[..i]) + multiset(s[i..])
{ }

lemma MultisetTake<T>(s: seq<T>, i: int)
  requires 0 <= i < |s|
  ensures multiset(s[..i+1]) == multiset(s[..i]) + multiset{s[i]}
{ }

method Insert(s: seq<int>, x: int) returns (res: seq<int>)
  requires forall i, j :: 0 <= i < j < |s| ==> s[i] <= s[j]
  ensures forall i, j :: 0 <= i < j < |res| ==> res[i] <= res[j]
  ensures |res| == |s| + 1
  ensures multiset(res) == multiset(s) + multiset{x}
{
  var i := 0;
  while i < |s| && s[i] < x
    invariant 0 <= i <= |s|
    invariant forall k :: 0 <= k < i ==> s[k] < x
  {
    i := i + 1;
  }
  MultisetSplit(s, i);
  res := s[..i] + [x] + s[i..];
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
  /* code modified by LLM (iteration 5): added lemma call to help prove multiset invariant */
  sorted := [];
  var i := 0;
  while i < |s|
    invariant 0 <= i <= |s|
    invariant forall k, l :: 0 <= k < l < |sorted| ==> sorted[k] <= sorted[l]
    invariant |sorted| == i
    invariant multiset(sorted) == multiset(s[..i])
  {
    MultisetTake(s, i);
    sorted := Insert(sorted, s[i]);
    i := i + 1;
  }
}
// </vc-code>
