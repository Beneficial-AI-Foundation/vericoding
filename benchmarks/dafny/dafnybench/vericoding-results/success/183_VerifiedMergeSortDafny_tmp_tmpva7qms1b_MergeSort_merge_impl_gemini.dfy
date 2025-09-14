// <vc-preamble>
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
// </vc-preamble>

// <vc-helpers>

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
  var i := 0;
  var j := 0;
  var k := start;
  while k < end
    invariant 0 <= i <= |a1|
    invariant 0 <= j <= |a2|
    invariant start <= k <= end
    invariant k == start + i + j
    invariant end - k == (|a1| - i) + (|a2| - j)
    invariant sorted_slice(b, start, k)
    invariant multiset(b[start..k]) == multiset(a1[..i]) + multiset(a2[..j])
    invariant forall m :: start <= m < k ==>
      (i < |a1| ==> b[m] <= a1[i]) && (j < |a2| ==> b[m] <= a2[j])
  {
    if j < |a2| && (i == |a1| || a2[j] < a1[i]) {
      b[k] := a2[j];
      j := j + 1;
    } else {
      b[k] := a1[i];
      i := i + 1;
    }
    k := k + 1;
  }
}
// </vc-code>
