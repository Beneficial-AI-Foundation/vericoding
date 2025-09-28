// <vc-preamble>
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method is_nested(s: seq<int>) returns (res: bool) 

    ensures res == exists x, y, z, w :: 0 <= x < y < z < w < |s| && s[x] == 0 && s[y] == 0 && s[z] == 1 && s[w] == 1
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 2): simplified to direct pattern search with proper invariants */
  var i := 0;
  while i < |s|
    invariant 0 <= i <= |s|
    invariant forall x, y, z, w :: 0 <= x < y < z < w < |s| && x < i && s[x] == 0 && s[y] == 0 && s[z] == 1 && s[w] == 1 ==> false
  {
    if s[i] == 0 {
      var j := i + 1;
      while j < |s|
        invariant i + 1 <= j <= |s|
        invariant forall y, z, w :: i < y < z < w < |s| && y < j && s[i] == 0 && s[y] == 0 && s[z] == 1 && s[w] == 1 ==> false
      {
        if s[j] == 0 {
          var k := j + 1;
          while k < |s|
            invariant j + 1 <= k <= |s|
            invariant forall z, w :: j < z < w < |s| && z < k && s[i] == 0 && s[j] == 0 && s[z] == 1 && s[w] == 1 ==> false
          {
            if s[k] == 1 {
              var l := k + 1;
              while l < |s|
                invariant k + 1 <= l <= |s|
                invariant forall w :: k < w < |s| && w < l && s[i] == 0 && s[j] == 0 && s[k] == 1 && s[w] == 1 ==> false
              {
                if s[l] == 1 {
                  assert s[i] == 0 && s[j] == 0 && s[k] == 1 && s[l] == 1;
                  assert 0 <= i < j < k < l < |s|;
                  return true;
                }
                l := l + 1;
              }
            }
            k := k + 1;
          }
        }
        j := j + 1;
      }
    }
    i := i + 1;
  }
  return false;
}
// </vc-code>
