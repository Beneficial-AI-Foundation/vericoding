// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 4): recursive index of minimum over indices divisible by 3 starting at i */
function min3Index(s: seq<int>, i: int): int
  requires 0 <= i < |s|
  requires i % 3 == 0
  ensures i <= min3Index(s, i) < |s|
  ensures min3Index(s, i) % 3 == 0
  ensures forall j :: i <= j < |s| && j % 3 == 0 ==> s[min3Index(s, i)] <= s[j]
  decreases (|s| - i + 2) / 3
{
  if i + 3 < |s| then
    if s[i] <= s[min3Index(s, i + 3)] then i else min3Index(s, i + 3)
  else
    i
}

// </vc-helpers>

// <vc-spec>
method sort_third(a: seq<int>) returns (sorted_even: seq<int>)

  requires |a| > 0

  ensures |sorted_even| == |a|
  ensures forall i, j :: 0 <= i < j < |sorted_even| && i % 3 == 0 && j % 3 == 0 ==>
      sorted_even[i] <= sorted_even[j]
  ensures forall i :: 0 <= i < |a| && i % 3 != 0 ==> sorted_even[i] == a[i]
  ensures multiset(a) == multiset(sorted_even)
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 4): changed loop guard to i + 3 <= |b| to maintain invariant and ensure at most one unprocessed index remains */
  var b := a;
  var i := 0;
  while i + 3 <= |b|
    invariant 0 <= i <= |b|
    invariant i % 3 == 0
    invariant |b| == |a|
    invariant multiset(b) == multiset(a)
    invariant forall p :: 0 <= p < |a| && p % 3 != 0 ==> b[p] == a[p]
    invariant forall p, q :: 0 <= p < q < i && p % 3 == 0 && q % 3 == 0 ==> b[p] <= b[q]
    invariant forall p :: 0 <= p < i && p % 3 == 0 ==> forall q :: i <= q < |b| && q % 3 == 0 ==> b[p] <= b[q]
    decreases (|b| - i + 2) / 3
  {
    var j := min3Index(b, i);
    var xi := b[i];
    var xj := b[j];
    b := b[i := xj];
    b := b[j := xi];
    i := i + 3;
  }
  sorted_even := b;
}
// </vc-code>
