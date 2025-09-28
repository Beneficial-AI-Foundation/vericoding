// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 4): changed function to method to fix type resolution errors */
method find_index(s: seq<int>, start: int, target: int) returns (idx: int)
    requires 0 <= start <= |s|
    ensures 0 <= idx <= |s|
    ensures idx == |s| || (start <= idx < |s| && s[idx] == target)
    ensures forall i :: start <= i < idx ==> s[i] != target
{
    if start == |s| {
        idx := |s|;
        return;
    }
    idx := start;
    while idx < |s| && s[idx] != target
        invariant start <= idx <= |s|
        invariant forall i :: start <= i < idx ==> s[i] != target
    {
        idx := idx + 1;
    }
}

predicate has_pattern(s: seq<int>, x: int, y: int, z: int, w: int)
    requires 0 <= x < y < z < w < |s|
{
    s[x] == 0 && s[y] == 0 && s[z] == 1 && s[w] == 1
}
// </vc-helpers>

// <vc-spec>
method is_nested(s: seq<int>) returns (res: bool) 

    ensures res == exists x, y, z, w :: 0 <= x < y < z < w < |s| && s[x] == 0 && s[y] == 0 && s[z] == 1 && s[w] == 1
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 5): changed algorithm to use while loop with first0 and simpler invariant */
    var first0 := find_index(s, 0, 0);
    while first0 < |s|
        invariant 0 <= first0 <= |s|
        invariant (forall x, y, z, w :: 0 <= x < y < z < w < |s| && s[x]==0 && s[y]==0 && s[z]==1 && s[w]==1 ==> x >= first0)
    {
        var second0 := find_index(s, first0+1, 0);
        if second0 < |s| {
            var first1 := find_index(s, second0+1, 1);
            if first1 < |s| {
                var second1 := find_index(s, first1+1, 1);
                if second1 < |s| {
                    return true;
                }
            }
        }
        first0 := find_index(s, first0+1, 0);
    }
    return false;
  }
// </vc-code>
