// verifies
// check that string between indexes low and high-1 are sorted
predicate Sorted(a: string, low:int, high:int)
requires 0 <= low <= high <= |a|
{ 
    forall j, k :: low <= j < k < high ==> a[j] <= a[k] 
}

// <vc-helpers>

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
  var x, y, z := a[0], a[1], a[2];
  
  // Sort three elements using comparisons
  if x <= y {
    if y <= z {
      // x <= y <= z
      b := [x, y, z];
    } else if x <= z {
      // x <= z < y
      b := [x, z, y];
    } else {
      // z < x <= y
      b := [z, x, y];
    }
  } else {
    // y < x
    if x <= z {
      // y < x <= z
      b := [y, x, z];
    } else if y <= z {
      // y <= z < x
      b := [y, z, x];
    } else {
      // z < y < x
      b := [z, y, x];
    }
  }
}
// </vc-code>

