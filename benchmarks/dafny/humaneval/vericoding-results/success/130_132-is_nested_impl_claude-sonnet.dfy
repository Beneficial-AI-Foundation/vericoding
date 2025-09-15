// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): Added helper predicate to check the nested pattern */
predicate HasNestedPattern(s: seq<int>, x: int, y: int, z: int, w: int)
{
  0 <= x < y < z < w < |s| && s[x] == 0 && s[y] == 0 && s[z] == 1 && s[w] == 1
}
// </vc-helpers>

// <vc-spec>
method is_nested(s: seq<int>) returns (res: bool) 

    ensures res == exists x, y, z, w :: 0 <= x < y < z < w < |s| && s[x] == 0 && s[y] == 0 && s[z] == 1 && s[w] == 1
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 2): Fixed loop invariants to maintain the complete postcondition */
  res := false;
  var i := 0;
  while i < |s|
    invariant 0 <= i <= |s|
    invariant res == exists x, y, z, w :: 0 <= x < y < z < w < |s| && s[x] == 0 && s[y] == 0 && s[z] == 1 && s[w] == 1 && x < i
  {
    if s[i] == 0 {
      var j := i + 1;
      while j < |s|
        invariant i + 1 <= j <= |s|
        invariant res == exists x, y, z, w :: 0 <= x < y < z < w < |s| && s[x] == 0 && s[y] == 0 && s[z] == 1 && s[w] == 1 && (x < i || (x == i && y < j))
      {
        if s[j] == 0 {
          var k := j + 1;
          while k < |s|
            invariant j + 1 <= k <= |s|
            invariant res == exists x, y, z, w :: 0 <= x < y < z < w < |s| && s[x] == 0 && s[y] == 0 && s[z] == 1 && s[w] == 1 && (x < i || (x == i && y < j) || (x == i && y == j && z < k))
          {
            if s[k] == 1 {
              var l := k + 1;
              while l < |s|
                invariant k + 1 <= l <= |s|
                invariant res == exists x, y, z, w :: 0 <= x < y < z < w < |s| && s[x] == 0 && s[y] == 0 && s[z] == 1 && s[w] == 1 && (x < i || (x == i && y < j) || (x == i && y == j && z < k) || (x == i && y == j && z == k && w < l))
              {
                if s[l] == 1 {
                  res := true;
                  assert HasNestedPattern(s, i, j, k, l);
                  return;
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
  assert !res ==> !exists x, y, z, w :: 0 <= x < y < z < w < |s| && s[x] == 0 && s[y] == 0 && s[z] == 1 && s[w] == 1;
}
// </vc-code>
