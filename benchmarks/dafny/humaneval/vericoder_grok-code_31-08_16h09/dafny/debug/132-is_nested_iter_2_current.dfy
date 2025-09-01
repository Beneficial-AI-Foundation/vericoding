

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
  var state := 0
  var i := 0
  while i < |s|
  {
    if state == 0 && s[i] == 0 { state := 1 }
    else if state == 1 && s[i] == 0 { state := 2 }
    else if state == 2 && s[i] == 1 { state := 3 }
    else if state == 3 && s[i] == 1 { return true }
    i := i + 1
  }
  return false
}
// </vc-code>

