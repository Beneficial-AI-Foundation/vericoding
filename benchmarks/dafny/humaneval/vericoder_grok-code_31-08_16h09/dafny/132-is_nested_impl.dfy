

// <vc-helpers>
// </vc-helpers>
// </vc-helpers>
// </vc-helpers>

// <vc-spec>
method is_nested(s: seq<int>) returns (res: bool) 
    // post-conditions-start
    ensures res == exists x, y, z, w :: 0 <= x < y < z < w < |s| && s[x] == 0 && s[y] == 0 && s[z] == 1 && s[w] == 1
    // post-conditions-end
// </vc-spec>
// <vc-code>
for x := 0 to |s|-1 {
    if s[x] == 0 {
      for y := x+1 to |s|-1 {
        if s[y] == 0 {
          for z := y+1 to |s|-1 {
            if s[z] == 1 {
              for w := z+1 to |s|-1 {
                if s[w] == 1 {
                  return true;
                }
              }
            }
          }
        }
      }
    }
  }
  return false;
// </vc-code>

