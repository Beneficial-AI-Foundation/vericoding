// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): predicate PresentUpTo records that all numbers < cur appear in first i elements */
predicate PresentUpTo(s: array<int>, i: int, cur: int)
  reads s
{
  0 <= i <= s.Length && 0 <= cur && (forall k :: 0 <= k < cur ==> exists j :: 0 <= j < i && s[j] == k)
}

/* helper modified by LLM (iteration 5): PresentUpTo preserved when increasing i */
lemma PresentUpTo_IncreaseI(s: array<int>, i: int, cur: int)
  requires PresentUpTo(s, i, cur)
  requires 0 <= i < s.Length
  ensures PresentUpTo(s, i + 1, cur)
{ }

/* helper modified by LLM (iteration 5): PresentUpTo extended when s[i]==cur */
lemma PresentUpTo_AddOne(s: array<int>, i: int, cur: int)
  requires PresentUpTo(s, i, cur)
  requires 0 <= i < s.Length
  requires s[i] == cur
  ensures PresentUpTo(s, i + 1, cur + 1)
{ }
// </vc-helpers>

// <vc-spec>
method SmallestMissingNumber(s: array<int>) returns (v: int)
    requires forall i, j :: 0 <= i < j < s.Length ==> s[i] <= s[j]
    requires forall i :: 0 <= i < s.Length ==> s[i] >= 0
    requires s.Length <= 100_000
    ensures 0 <= v
    ensures forall i :: 0 <= i < s.Length ==> s[i] != v
    ensures forall k {:trigger} :: 0 <= k < v ==> exists j :: 0 <= j < s.Length && s[j] == k
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 5): linear scan using helper lemmas to maintain PresentUpTo */
  var i := 0;
  var cur := 0;
  while i < s.Length && s[i] <= cur
    invariant 0 <= i <= s.Length
    invariant 0 <= cur
    invariant PresentUpTo(s, i, cur)
    invariant forall j :: 0 <= j < i ==> s[j] <= cur
    invariant forall j :: 0 <= j < i ==> s[j] != cur
    decreases s.Length - i
  {
    if s[i] == cur {
      PresentUpTo_AddOne(s, i, cur);
      i := i + 1;
      cur := cur + 1;
    } else {
      PresentUpTo_IncreaseI(s, i, cur);
      i := i + 1;
    }
  }
  v := cur;
}
// </vc-code>
