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
  res := false;
  
  if |s| < 4 {
    return;
  }
  
  var x := 0;
  while x < |s| - 3
    invariant 0 <= x <= |s| - 3
    invariant !res ==> forall x', y', z', w' :: 0 <= x' < x && x' < y' < z' < w' < |s| ==> !(s[x'] == 0 && s[y'] == 0 && s[z'] == 1 && s[w'] == 1)
  {
    if s[x] == 0 {
      var y := x + 1;
      while y < |s| - 2
        invariant x < y <= |s| - 2
        invariant !res ==> forall y', z', w' :: x < y' < y && y' < z' < w' < |s| ==> !(s[x] == 0 && s[y'] == 0 && s[z'] == 1 && s[w'] == 1)
      {
        if s[y] == 0 {
          var z := y + 1;
          while z < |s| - 1
            invariant y < z <= |s| - 1
            invariant !res ==> forall z', w' :: y < z' < z && z' < w' < |s| ==> !(s[x] == 0 && s[y] == 0 && s[z'] == 1 && s[w'] == 1)
          {
            if s[z] == 1 {
              var w := z + 1;
              while w < |s|
                invariant z < w <= |s|
                invariant !res ==> forall w' :: z < w' < w ==> !(s[x] == 0 && s[y] == 0 && s[z] == 1 && s[w'] == 1)
              {
                if s[w] == 1 {
                  res := true;
                  return;
                }
                w := w + 1;
              }
            }
            z := z + 1;
          }
        }
        y := y + 1;
      }
    }
    x := x + 1;
  }
}
// </vc-code>
