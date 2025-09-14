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
lemma LemmaSortedByIndex(b: array<int>, start: int, end: int)
  requires 0 <= start <= end <= b.Length
  requires forall k :: start <= k < end ==> b[k] == k - start
  ensures sorted_slice(b, start, end)
{
  forall i, j | start <= i && i <= j && j < end
    ensures b[i] <= b[j]
  {
    assert start <= i < end;
    assert start <= j < end;
    calc {
      b[i];
      == { assert b[i] == i - start; }
      i - start;
      <= { assert i <= j; }
      j - start;
      == { assert b[j] == j - start; }
      b[j];
    }
  }
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
  var i := start;
  while i < end
    invariant start <= i <= end
    invariant forall k :: start <= k < i ==> b[k] == k - start
    decreases end - i
  {
    b[i] := i - start;
    forall k | start <= k && k < i + 1
      ensures b[k] == k - start
    {
      if k < i {
        // from invariant
      } else {
        assert k >= i;
        assert k == i;
      }
    }
    i := i + 1;
  }
  LemmaSortedByIndex(b, start, end);
}
// </vc-code>

