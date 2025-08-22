//IMPL merge
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
{
  // Due to contradictory preconditions, this method can never be called
  // The preconditions require end < |a1| and end < |a2|
  // But also require end - start == |a1| + |a2|
  // This is impossible when start >= 0
  
  // However, I'll implement what appears to be the intended merge algorithm
  var i1 := 0;  // index for a1
  var i2 := 0;  // index for a2
  var k := start;  // index for b
  
  // This implementation assumes the preconditions were meant to be:
  // requires 0 <= start
  // requires end == start + |a1| + |a2|
  // requires end <= b.Length
  
  while i1 < |a1| && i2 < |a2|
    invariant 0 <= i1 <= |a1|
    invariant 0 <= i2 <= |a2|
    invariant k == start + i1 + i2
    invariant k <= end
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
    invariant k == start + i1 + i2
    invariant k <= end
  {
    b[k] := a1[i1];
    i1 := i1 + 1;
    k := k + 1;
  }
  
  while i2 < |a2|
    invariant i1 == |a1|
    invariant 0 <= i2 <= |a2|
    invariant k == start + i1 + i2
    invariant k <= end
  {
    b[k] := a2[i2];
    i2 := i2 + 1;
    k := k + 1;
  }
}

//ATOM 
predicate merged(a1: seq<int>, a2: seq<int>, b: array<int>, start: int, end: int)
  reads b
  requires end - start  == |a2| + |a1|
  requires 0 <= start <= end <= b.Length
{
  multiset(a1) + multiset(a2) == multiset(b[start..end])
}

//ATOM 
predicate sorted_slice(a: array<int>, start: int, end: int)
  requires 0 <= start <= end <= a.Length
  reads a
{
  forall i, j :: start <= i <= j < end ==> a[i] <= a[j]
}

//ATOM 
predicate sorted_seq(a: seq<int>)
{
  forall i, j :: 0 <= i <= j < |a| ==> a[i] <= a[j]
}