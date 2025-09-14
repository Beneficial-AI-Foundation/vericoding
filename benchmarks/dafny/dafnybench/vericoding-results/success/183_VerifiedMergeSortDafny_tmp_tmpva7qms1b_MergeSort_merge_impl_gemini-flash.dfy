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
lemma lemma_append_sorted_slices(s1: seq<int>, s2: seq<int>)
  requires sorted_seq(s1)
  requires sorted_seq(s2)
  requires |s1| == 0 || |s2| == 0 || s1[|s1|-1] <= s2[0]
  ensures sorted_seq(s1 + s2)
{
}
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
        invariant start <= k <= end
        invariant 0 <= i <= |a1|
        invariant 0 <= j <= |a2|
        invariant k - start == i + j
        invariant merged(a1[0..i], a2[0..j], b, start, k)
        invariant sorted_slice(b, start, k)
    {
        if i < |a1| && (j == |a2| || a1[i] <= a2[j]) {
            b[k] := a1[i];
            i := i + 1;
        } else {
            b[k] := a2[j];
            j := j + 1;
        }
        k := k + 1;
    }
}
// </vc-code>

