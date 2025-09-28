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
/* helper modified by LLM (iteration 5): added multiset invariant to maintain postcondition for element insertion */
method InsertSorted(s: seq<int>, e: int) returns (res: seq<int>)
  requires forall i, j :: 0 <= i < j < |s| ==> s[i] <= s[j]
  ensures forall i, j :: 0 <= i < j < |res| ==> res[i] <= res[j]
  ensures multiset(s) + multiset{e} == multiset(res)
{
  var i: int := 0;
  while i < |s| && s[i] <= e
    invariant 0 <= i <= |s|
    invariant forall p :: 0 <= p < i ==> s[p] <= e
    invariant multiset(s[..i]) + multiset{e} == multiset(s[..i] + [e] + s[i..])
  {
    i := i + 1;
  }
  res := s[..i] + [e] + s[i..];
}
// </vc-helpers>

// <vc-spec>
method SortSeq(s: seq<int>) returns (sorted: seq<int>)

  ensures forall i, j :: 0 <= i < j < |sorted| ==> sorted[i] <= sorted[j]
  ensures |sorted| == |s|
  ensures multiset(s) == multiset(sorted)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): retained multiset invariant in loop for verification, added length invariant for clarity */
{
  sorted := [];
  for i := 0 to |s|-1
    invariant 0 <= i <= |s|
    invariant |sorted| == i
    invariant forall p, q :: 0 <= p < q < |sorted| ==> sorted[p] <= sorted[q]
    invariant multiset(s[..i]) == multiset(sorted)
  {
    sorted := InsertSorted(sorted, s[i]);
  }
}
// </vc-code>
