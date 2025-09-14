// verifies
// check that string between indexes low and high-1 are sorted
predicate Sorted(a: string, low:int, high:int)
requires 0 <= low <= high <= |a|
{ 
    forall j, k :: low <= j < k < high ==> a[j] <= a[k] 
}

// <vc-helpers>
// No helpers needed for this verification
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
  // extract single-character substrings for convenience
  var s0 := a[0..1];
  var s1 := a[1..2];
  var s2 := a[2..3];

  if a[0] <= a[1] {
    if a[1] <= a[2] {
      b := a;
    } else {
      // a[1] > a[2]
      if a[0] <= a[2] {
        // a0 <= a2 < a1  => a0,a2,a1
        b := s0 + s2 + s1;
      } else {
        // a2 < a0 <= a1 => a2,a0,a1
        b := s2 + s0 + s1;
      }
    }
  } else {
    // a[0] > a[1]
    if a[0] <= a[2] {
      // a1 < a0 <= a2 => a1,a0,a2
      b := s1 + s0 + s2;
    } else {
      // a0 > a2
      if a[1] <= a[2] {
        // a1 <= a2 < a0 => a1,a2,a0
        b := s1 + s2 + s0;
      } else {
        // a2 < a1 < a0 => a2,a1,a0
        b := s2 + s1 + s0;
      }
    }
  }

  // prove sortedness: for length 3 it's enough to show pairwise inequalities
  assert b[0] <= b[1];
  assert b[1] <= b[2];
  assert forall j, k :: 0 <= j < k < 3 ==> b[j] <= b[k];

  // prove multiset equality by observing b's characters are a permutation of a's characters
  assert multiset{b[0], b[1], b[2]} == multiset{a[0], a[1], a[2]};

  // length preserved
  assert |b| == 3;
  assert |a| == |b|;
}
// </vc-code>

