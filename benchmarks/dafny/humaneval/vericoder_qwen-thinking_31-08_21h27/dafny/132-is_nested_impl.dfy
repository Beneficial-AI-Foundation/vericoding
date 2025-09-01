

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method is_nested(s: seq<int>) returns (res: bool) 
    // post-conditions-start
    ensures res == exists x, y, z, w :: 0 <= x < y < z < w < |s| && s[x] == 0 && s[y] == 0 && s[z] == 1 && s[w] == 1
    // post-conditions-end
// </vc-spec>
// <vc-code>
{
  if |s| < 4 {
    return false;
  }

  var i := 0;
  while i < |s| && s[i] != 0
    invariant 0 <= i <= |s|
    invariant forall p :: 0 <= p < i ==> s[p] != 0
  {
    i := i + 1;
  }
  if i == |s| {
    return false;
  }

  var j := i + 1;
  while j < |s| && s[j] != 0
    invariant i+1 <= j <= |s|
    invariant forall p :: i < p < j ==> s[p] != 0
  {
    j := j + 1;
  }
  if j == |s| {
    return false;
  }

  var count := 0;
  var k := j + 1;
  ghost var expected := 0;
  while k < |s|
    invariant count == s[j+1..k].Count(1)
  {
    if s[k] == 1 {
      count := count + 1;
    }
    k := k + 1;
  }
  return count >= 2;
}
// </vc-code>

