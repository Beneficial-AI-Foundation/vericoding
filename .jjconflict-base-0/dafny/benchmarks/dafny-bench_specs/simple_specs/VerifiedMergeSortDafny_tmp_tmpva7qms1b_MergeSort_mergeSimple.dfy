//ATOM

predicate sorted_seq(a: seq<int>)
{
 forall i, j :: 0 <= i <= j < |a| ==> a[i] <= a[j]
}


//ATOM

predicate sorted_slice(a: array<int>, start: int, end: int)
 requires 0 <= start <= end <= a.Length
 reads a
{
 forall i, j :: start <= i <= j < end ==> a[i] <= a[j]
}


// SPEC
method mergeSimple(a1: seq<int>, a2: seq<int>, start: int, end: int, b: array<int>)
 modifies b
 requires sorted_seq(a1)
 requires sorted_seq(a2)
 requires 0 <= start <= end <= b.Length
 requires |a1| + |a2| == end - start + 1
 ensures sorted_slice(b, start, end)
{
}
