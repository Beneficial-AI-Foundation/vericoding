

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
  var n := |s|;
  if n < 4 { return false; }
  var i := 0;
  while i <= n - 4
    invariant 0 <= i <= n
    invariant forall x,y,z,w :: 0 <= x < y < z < w < n && x < i ==> !(s[x] == 0 && s[y] == 0 && s[z] == 1 && s[w] == 1)
    decreases n - i
  {
    var j := i + 1;
    while j <= n - 3
      invariant 0 <= j <= n
      invariant forall x,y,z,w :: 0 <= x < y < z < w < n && (x < i || (x == i && y < j)) ==> !(s[x] == 0 && s[y] == 0 && s[z] == 1 && s[w] == 1)
      decreases n - j
    {
      var k := j + 1;
      while k <= n - 2
        invariant 0 <= k <= n
        invariant forall x,y,z,w :: 0 <= x < y < z < w < n && (x < i || (x == i && y < j) || (x == i && y == j && z < k)) ==> !(s[x] == 0 && s[y] == 0 && s[z] == 1 && s[w] == 1)
        decreases n - k
      {
        var l := k + 1;
        while l <= n - 1
          invariant 0 <= l <= n
          invariant forall x,y,z,w :: 0 <= x < y < z < w < n && (x < i || (x == i && y < j) || (x == i && y == j && z < k) || (x == i && y == j && z == k && w < l)) ==> !(s[x] == 0 && s[y] == 0 && s[z] == 1 && s[w] == 1)
          decreases n - l
        {
          if s[i] == 0 && s[j] == 0 && s[k] == 1 && s[l] == 1 {
            return true;
          }
          l := l + 1;
        }
        k := k + 1;
      }
      j := j + 1;
    }
    i := i + 1;
  }
  return false;
}
// </vc-code>

