// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
function FindPattern(s: seq<int>): (found: bool)
  ensures found == exists x, y, z, w :: 0 <= x < y < z < w < |s| && s[x] == 0 && s[y] == 0 && s[z] == 1 && s[w] == 1
{
  if |s| < 4 then
    false
  else
    exists x, y, z, w :: 0 <= x < y < z < w < |s| && s[x] == 0 && s[y] == 0 && s[z] == 1 && s[w] == 1
}
// </vc-helpers>

// <vc-spec>
method is_nested(s: seq<int>) returns (res: bool) 

    ensures res == exists x, y, z, w :: 0 <= x < y < z < w < |s| && s[x] == 0 && s[y] == 0 && s[z] == 1 && s[w] == 1
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 4): Fixed syntax error in helper function */
  res := FindPattern(s);
}
// </vc-code>
