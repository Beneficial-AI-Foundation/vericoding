

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
    var zeros_seen := 0;
    var ones_after_two_zeros := 0;
    
    var i := 0;
    while i < |s|
        invariant 0 <= i <= |s|
        invariant zeros_seen >= 0
        invariant ones_after_two_zeros >= 0
        invariant res == (ones_after_two_zeros >= 2)
        invariant !res ==> (forall x, y, z, w :: 0 <= x < y < z < w < i ==> !(s[x] == 0 && s[y] == 0 && s[z] == 1 && s[w] == 1))
        invariant res ==> (exists x, y, z, w :: 0 <= x < y < z < w < i && s[x] == 0 && s[y] == 0 && s[z] == 1 && s[w] == 1)
    {
        if s[i] == 0 {
            zeros_seen := zeros_seen + 1;
        } else if s[i] == 1 {
            if zeros_seen >= 2 {
                ones_after_two_zeros := ones_after_two_zeros + 1;
                if ones_after_two_zeros >= 2 {
                    res := true;
                }
            }
        }
        i := i + 1;
    }
}
// </vc-code>

