// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): added decreases clause to fix termination */
function FindFirst(s: seq<int>, start: nat, target: int): (idx: int)
    requires 0 <= start <= |s|
    ensures start <= idx <= |s|
    ensures idx < |s| ==> s[idx] == target
    ensures forall i :: start <= i < idx ==> s[i] != target
    decreases |s| - start
{
    if start == |s| then
        |s|
    else if s[start] == target then
        start
    else
        FindFirst(s, start + 1, target)
}

function ExistsPattern(s: seq<int>): bool
{
    var x := FindFirst(s, 0, 0);
    if x == |s| then false else
    var y := FindFirst(s, x + 1, 0);
    if y == |s| then false else
    var z := FindFirst(s, y + 1, 1);
    if z == |s| then false else
    var w := FindFirst(s, z + 1, 1);
    w < |s|
}
// </vc-helpers>

// <vc-spec>
method is_nested(s: seq<int>) returns (res: bool) 

    ensures res == exists x, y, z, w :: 0 <= x < y < z < w < |s| && s[x] == 0 && s[y] == 0 && s[z] == 1 && s[w] == 1
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 2): no change needed, uses fixed helper */
  res := ExistsPattern(s);
}
// </vc-code>
