predicate merged(a1: seq<int>, a2: seq<int>, b: array<int>, start: int, end: int)
  reads b
  requires end - start  == |a2| + |a1|
  requires 0 <= start <= end <= b.Length
{
  multiset(a1) + multiset(a2) == multiset(b[start..end])
}

predicate sorted_slice(a: array<int>, start: int, end: int)
  requires 0 <= start <= end <= a.Length
  reads a
{
  forall i, j :: start <= i <= j < end ==> a[i] <= a[j]
}

predicate sorted_seq(a: seq<int>)
{
  forall i, j :: 0 <= i <= j < |a| ==> a[i] <= a[j]
}

predicate sorted(a: array<int>)
  reads a
{
  forall i, j :: 0 <= i < j < a.Length ==> a[i] <= a[j]
}

// <vc-helpers>
// No additional helpers needed; the provided predicates suffice.
// </vc-helpers>

// <vc-spec>
method merge(a1: seq<int>, a2: seq<int>, start: int, end: int, b: array<int>)
  modifies b
  requires sorted_seq(a1)
  requires sorted_seq(a2)
  requires end - start == |a1| + |a2|
  requires 0 <= start < end < |a1| && end <= |a2| < b.Length
  requires end < |a1| && end < |a2|
  ensures sorted_slice(b, start, end)
  requires b.Length == |a2| + |a1|
  ensures merged(a1, a2, b, start, end)
// </vc-spec>
// <vc-code>
{
  var i1 := 0;
  var i2 := 0;
  var k := start;
  while i1 < |a1| && i2 < |a2|
    invariant 0 <= i1 <= |a1|
    invariant 0 <= i2 <= |a2|
    invariant start <= k <= end
    invariant k == start + i1 + i2
    invariant sorted_slice(b, start, k)
    invariant multiset(a1) + multiset(a2) == multiset(b[start..k]) + multiset(a1[i1..]) + multiset(a2[i2..])
  {
    if a1[i1] <= a2[i2] {
      b[k] := a1[i1];
      i1 := i1 + 1;
    } else {
      b[k] := a2[i2];
      i2 := i2 + 1;
    }
    k := k + 1;
  }
  while i1 < |a1|
    invariant 0 <= i1 <= |a1|
    invariant i2 == |a2|
    invariant start + |a1| <= k <= end
    invariant k == start + i1 + |a2|
    invariant sorted_slice(b, start, k)
    invariant multiset(a1) + multiset(a2) == multiset(b[start..k]) + multiset(a1[i1..])
  {
    b[k] := a1[i1];
    i1 := i1 + 1;
    k := k + 1;
  }
  while i2 < |a2|
    invariant i1 == |a1|
    invariant 0 <= i2 <= |a2|
    invariant start + |a1| <= k <= end
    invariant k == start + |a1| + i2
    invariant sorted_slice(b, start, k)
    invariant multiset(a1) + multiset(a2) == multiset(b[start..k]) + multiset(a2[i2..])
  {
    b[k] := a2[i2];
    i2 := i2 + 1;
    k := k + 1;
  }
}
// </vc-code>

