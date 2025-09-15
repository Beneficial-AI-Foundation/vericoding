// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
function IsNested(s: seq<int>): bool { exists x:int, y:int, z:int, w:int :: 0 <= x < y < z < w < |s| && s[x] == 0 && s[y] == 0 && s[z] == 1 && s[w] == 1 }
// </vc-helpers>

// <vc-spec>
method is_nested(s: seq<int>) returns (res: bool) 

    ensures res == exists x, y, z, w :: 0 <= x < y < z < w < |s| && s[x] == 0 && s[y] == 0 && s[z] == 1 && s[w] == 1
// </vc-spec>
// <vc-code>
{
  res := IsNested(s);
}
// </vc-code>
