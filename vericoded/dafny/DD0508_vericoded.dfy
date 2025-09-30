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
lemma sorted_seq_property(a: seq<int>, i: int, j: int)
  requires sorted_seq(a)
  requires 0 <= i <= j < |a|
  ensures a[i] <= a[j]
{
}
// </vc-helpers>

// <vc-spec>
method mergeSimple(a1: seq<int>, a2: seq<int>, start: int, end: int, b: array<int>)
  modifies b
  requires sorted_seq(a1)
  requires sorted_seq(a2)
  requires 0 <= start <= end <= b.Length
  requires |a1| +  |a2| == end - start + 1
  ensures sorted_slice(b, start, end)
// </vc-spec>
// <vc-code>
{
  if |a1| + |a2| == 0 {
    return;
  }
  
  var i1 := 0;
  var i2 := 0;
  var k := start;
  
  // Since |a1| + |a2| == end - start + 1, we actually have one more element
  // than positions in b[start..end]. We'll adjust by filling up to end-1.
  
  while k < end && (i1 < |a1| || i2 < |a2|)
    invariant start <= k <= end
    invariant 0 <= i1 <= |a1|
    invariant 0 <= i2 <= |a2|
    invariant k - start == i1 + i2
    invariant forall p, q :: start <= p <= q < k ==> b[p] <= b[q]
    invariant i1 > 0 && k > start ==> forall p :: 0 <= p < i1 ==> a1[p] <= b[k-1]
    invariant i2 > 0 && k > start ==> forall p :: 0 <= p < i2 ==> a2[p] <= b[k-1]
    invariant i1 < |a1| ==> forall p :: start <= p < k ==> b[p] <= a1[i1]
    invariant i2 < |a2| ==> forall p :: start <= p < k ==> b[p] <= a2[i2]
  {
    if i1 < |a1| && (i2 >= |a2| || a1[i1] <= a2[i2]) {
      b[k] := a1[i1];
      i1 := i1 + 1;
    } else if i2 < |a2| {
      b[k] := a2[i2];
      i2 := i2 + 1;
    }
    k := k + 1;
  }
}
// </vc-code>

