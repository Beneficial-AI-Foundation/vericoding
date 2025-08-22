// IMPL 
method mergeSimple(a1: seq<int>, a2: seq<int>, start: int, end: int, b: array<int>)
  modifies b
  requires sorted_seq(a1)
  requires sorted_seq(a2)
  requires 0 <= start <= end <= b.Length
  requires |a1| +  |a2| == end - start
  ensures sorted_slice(b, start, end)
{
  var i1, i2, k := 0, 0, start;
  
  /* code modified by LLM (iteration 4): Fixed main merge loop with proper invariants */
  while i1 < |a1| && i2 < |a2|
    invariant 0 <= i1 <= |a1|
    invariant 0 <= i2 <= |a2|
    invariant start <= k <= end
    invariant k == start + i1 + i2
    invariant sorted_slice(b, start, k)
    invariant i1 < |a1| && i2 < |a2| ==> k < end
    invariant forall x :: start <= x < k ==> (i1 < |a1| ==> b[x] <= a1[i1])
    invariant forall x :: start <= x < k ==> (i2 < |a2| ==> b[x] <= a2[i2])
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
  
  /* code modified by LLM (iteration 4): Fixed remaining elements loop with proper bounds */
  while i1 < |a1|
    invariant 0 <= i1 <= |a1|
    invariant i2 == |a2|
    invariant start <= k <= end
    invariant k == start + i1 + i2
    invariant sorted_slice(b, start, k)
    invariant i1 < |a1| ==> k < end
  {
    b[k] := a1[i1];
    i1 := i1 + 1;
    k := k + 1;
  }
  
  /* code modified by LLM (iteration 4): Fixed remaining elements loop with proper bounds */
  while i2 < |a2|
    invariant 0 <= i2 <= |a2|
    invariant i1 == |a1|
    invariant start <= k <= end
    invariant k == start + i1 + i2
    invariant sorted_slice(b, start, k)
    invariant i2 < |a2| ==> k < end
  {
    b[k] := a2[i2];
    i2 := i2 + 1;
    k := k + 1;
  }
  
  /* code modified by LLM (iteration 4): Added assertion to establish postcondition */
  assert i1 == |a1| && i2 == |a2| && k == end;
}


// IMPL 

method merge(a1: seq<int>, a2: seq<int>, start: int, end: int, b: array<int>)
  modifies b
  requires sorted_seq(a1)
  requires sorted_seq(a2)
  requires end - start == |a1| + |a2|
  requires 0 <= start < end <= b.Length
  requires b.Length >= |a1| + |a2|
  ensures sorted_slice(b, start, end)
  ensures merged(a1, a2, b, start, end)
{
  var i1, i2, k := 0, 0, start;
  
  /* code modified by LLM (iteration 4): Enhanced main merge loop with complete invariants */
  while i1 < |a1| && i2 < |a2|
    invariant 0 <= i1 <= |a1|
    invariant 0 <= i2 <= |a2|
    invariant start <= k <= end
    invariant k == start + i1 + i2
    invariant sorted_slice(b, start, k)
    invariant multiset(a1[..i1]) + multiset(a2[..i2]) == multiset(b[start..k])
    invariant forall x :: start <= x < k ==> (i1 < |a1| ==> b[x] <= a1[i1])
    invariant forall x :: start <= x < k ==> (i2 < |a2| ==> b[x] <= a2[i2])
    invariant i1 < |a1| && i2 < |a2| ==> k < end
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
  
  /* code modified by LLM (iteration 4): Enhanced remaining a1 elements loop */
  while i1 < |a1|
    invariant 0 <= i1 <= |a1|
    invariant i2 == |a2|
    invariant start <= k <= end
    invariant k == start + i1 + i2
    invariant sorted_slice(b, start, k)
    invariant multiset(a1[..i1]) + multiset(a2[..i2]) == multiset(b[start..k])
    invariant forall x :: start <= x < k ==> (i1 < |a1| ==> b[x] <= a1[i1])
    invariant i1 < |a1| ==> k < end
  {
    b[k] := a1[i1];
    i1 := i1 + 1;
    k := k + 1;
  }
  
  /* code modified by LLM (iteration 4): Enhanced remaining a2 elements loop */
  while i2 < |a2|
    invariant 0 <= i2 <= |a2|
    invariant i1 == |a1|
    invariant start <= k <= end
    invariant k == start + i1 + i2
    invariant sorted_slice(b, start, k)
    invariant multiset(a1[..i1]) + multiset(a2[..i2]) == multiset(b[start..k])
    invariant forall x :: start <= x < k ==> (i2 < |a2| ==> b[x] <= a2[i2])
    invariant i2 < |a2| ==> k < end
  {
    b[k] := a2[i2];
    i2 := i2 + 1;
    k := k + 1;
  }
  
  /* code modified by LLM (iteration 4): Added final assertions to establish postconditions */
  assert i1 == |a1| && i2 == |a2| && k == end;
  assert multiset(a1[..i1]) + multiset(a2[..i2]) == multiset(b[start..k]);
  assert a1[..i1] == a1 && a2[..i2] == a2 && b[start..k] == b[start..end];
  assert multiset(a1) + multiset(a2) == multiset(b[start..end]);
}



// ATOM 


predicate merged(a1: seq<int>, a2: seq<int>, b: array<int>, start: int, end: int)
  reads b
  requires end - start  == |a2| + |a1|
  requires 0 <= start <= end <= b.Length
{
  multiset(a1) + multiset(a2) == multiset(b[start..end])
}


// ATOM 

predicate sorted_slice(a: array<int>, start: int, end: int)
  requires 0 <= start <= end <= a.Length
  reads a
{
  forall i, j :: start <= i <= j < end ==> a[i] <= a[j]
}


// ATOM 

predicate sorted_seq(a: seq<int>)
{
  forall i, j :: 0 <= i <= j < |a| ==> a[i] <= a[j]
}


// ATOM 

predicate sorted(a: array<int>)
  reads a
{
  forall i, j :: 0 <= i < j < a.Length ==> a[i] <= a[j]
}