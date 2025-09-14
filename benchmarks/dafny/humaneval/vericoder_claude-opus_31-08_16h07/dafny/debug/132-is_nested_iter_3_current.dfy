

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
    var i := 0;
    
    while i < |s| && !res
        invariant 0 <= i <= |s|
        invariant !res ==> (forall x, y, z, w :: 0 <= x < y < z < w < i ==> !(s[x] == 0 && s[y] == 0 && s[z] == 1 && s[w] == 1))
        invariant res ==> (exists x, y, z, w :: 0 <= x < y < z < w < |s| && s[x] == 0 && s[y] == 0 && s[z] == 1 && s[w] == 1)
    {
        if i + 1 < |s| && s[i] == 0 && s[i+1] == 0 {
            // Found two consecutive zeros at positions i and i+1
            // Now look for two consecutive ones after position i+1
            var j := i + 2;
            while j < |s| && !res
                invariant i + 2 <= j <= |s|
                invariant !res ==> (forall z, w :: i + 2 <= z < w < j ==> !(s[z] == 1 && s[w] == 1))
                invariant res ==> (exists z, w :: i + 2 <= z < w < |s| && s[z] == 1 && s[w] == 1)
                invariant res ==> s[i] == 0 && s[i+1] == 0
                invariant res ==> (exists z, w :: i + 2 <= z < w < |s| && s[z] == 1 && s[w] == 1 && 
                                   i < i+1 && i+1 < z && z < w)
            {
                if j + 1 < |s| && s[j] == 1 && s[j+1] == 1 {
                    // Found the pattern: s[i] == 0, s[i+1] == 0, s[j] == 1, s[j+1] == 1
                    // where i < i+1 < j < j+1
                    assert i < i+1 < j < j+1 < |s|;
                    assert s[i] == 0 && s[i+1] == 0 && s[j] == 1 && s[j+1] == 1;
                    res := true;
                }
                j := j + 1;
            }
        }
        i := i + 1;
    }
}
// </vc-code>

