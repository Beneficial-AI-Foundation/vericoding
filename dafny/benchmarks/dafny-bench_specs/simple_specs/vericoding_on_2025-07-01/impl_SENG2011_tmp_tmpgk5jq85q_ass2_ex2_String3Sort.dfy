//ATOM

// verifies
// check that string between indexes low and high-1 are sorted
predicate Sorted(a: string, low:int, high:int)
requires 0 <= low <= high <= |a|
{ 
  forall j, k :: low <= j < k < high ==> a[j] <= a[k] 
}


// SPEC

method String3Sort(a: string) returns (b: string) 
requires |a| == 3
ensures Sorted(b, 0, |b|)
ensures |a| == |b|
ensures multiset{
}

{
}