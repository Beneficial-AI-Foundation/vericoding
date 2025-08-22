//ATOM
// verifies
// check that string between indexes low and high-1 are sorted
predicate Sorted(a: string, low:int, high:int)
requires 0 <= low <= high <= |a|
{ 
  forall j, k :: low <= j < k < high ==> a[j] <= a[k] 
}

//ATOM
method String3Sort(a: string) returns (b: string) 
requires |a| == 3
ensures Sorted(b, 0, |b|)
ensures |a| == |b|
ensures multiset{b[0], b[1], b[2]} == multiset{a[0], a[1], a[2]}
{
  // Sort the 3 characters
  var c0, c1, c2 := a[0], a[1], a[2];
  
  // Simple sorting network for 3 elements
  if c0 > c1 { c0, c1 := c1, c0; }
  if c1 > c2 { c1, c2 := c2, c1; }
  if c0 > c1 { c0, c1 := c1, c0; }
  
  b := [c0, c1, c2];
}

//IMPL check
method check() 
{
}