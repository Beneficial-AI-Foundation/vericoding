// verifies
// check that string between indexes low and high-1 are sorted
predicate Sorted(a: string, low:int, high:int)
requires 0 <= low <= high <= |a|
{ 
    forall j, k :: low <= j < k < high ==> a[j] <= a[k] 
}

// <vc-helpers>
predicate Sorted(a: string, low: int, high: int)
  requires 0 <= low <= high <= |a|
{
  forall j, k :: low <= j < k < high ==> a[j] <= a[k]
}
// </vc-helpers>

// <vc-spec>
method String3Sort(a: string) returns (b: string) 
requires |a| == 3;
ensures Sorted(b, 0, |b|);
ensures |a| == |b|;
ensures multiset{b[0], b[1], b[2]} == multiset{a[0], a[1], a[2]};
// </vc-spec>
// <vc-code>
{
  var s0 := a[0];
  var s1 := a[1];
  var s2 := a[2];
  if s0 > s1 {
    s0, s1 := s1, s0;
  }
  if s1 > s2 {
    s1, s2 := s2, s1;
  }
  if s0 > s1 {
    s0, s1 := s1, s0;
  }
  b := [s0, s1, s2];
  assert |a| == |b| && multiset(a) == multiset(b) && Sorted(b, 0, |b|);
}
// </vc-code>

