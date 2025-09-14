// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
function FindIndex(s: seq<int>, val: int, start: int): (r: int)
  requires 0 <= start <= |s|
  ensures start <= r <= |s|
  ensures r < |s| ==> s[r] == val
  ensures forall i :: start <= i < r ==> s[i] != val
  decreases |s| - start
{
  if start == |s| then
    |s|
  else if s[start] == val then
    start
  else
    FindIndex(s, val, start + 1)
}
// </vc-helpers>

// <vc-spec>
method is_nested(s: seq<int>) returns (res: bool) 

    ensures res == exists x, y, z, w :: 0 <= x < y < z < w < |s| && s[x] == 0 && s[y] == 0 && s[z] == 1 && s[w] == 1
// </vc-spec>
// <vc-code>
{
  res := false;
  var x := FindIndex(s, 0, 0);
  if x < |s| {
    var y := FindIndex(s, 0, x + 1);
    if y < |s| {
      var z := FindIndex(s, 1, y + 1);
      if z < |s| {
        var w := FindIndex(s, 1, z + 1);
        if w < |s| {
          res := true;
        }
      }
    }
  }
}
// </vc-code>
