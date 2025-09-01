

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
        invariant res ==> (exists x, y, z, w :: 0 <= x < y < z < w < |s| && s[x] == 0 && s[y] == 0 && s[z] == 1 && s[w] == 1)
        invariant !res ==> (forall x, y, z, w :: 0 <= x < y < z < w < |s| && x < i ==> !(s[x] == 0 && s[y] == 0 && s[z] == 1 && s[w] == 1))
    {
        if i + 3 < |s| && s[i] == 0 {
            var j := i + 1;
            while j < |s| && !res && s[j] == 0
                invariant i + 1 <= j <= |s|
                invariant res ==> (exists x, y, z, w :: 0 <= x < y < z < w < |s| && s[x] == 0 && s[y] == 0 && s[z] == 1 && s[w] == 1)
                invariant !res && j < |s| ==> s[j] == 0
            {
                // j is the position of a second 0
                var k := j + 1;
                while k < |s| && !res
                    invariant j + 1 <= k <= |s|
                    invariant res ==> (exists x, y, z, w :: 0 <= x < y < z < w < |s| && s[x] == 0 && s[y] == 0 && s[z] == 1 && s[w] == 1)
                    invariant !res ==> (forall z, w :: j < z < k && z < w < |s| && s[z] == 1 && s[w] == 1 ==> !(s[i] == 0 && s[j] == 0))
                {
                    if k + 1 < |s| && s[k] == 1 && s[k+1] == 1 {
                        assert i < j < k < k+1 < |s|;
                        assert s[i] == 0 && s[j] == 0 && s[k] == 1 && s[k+1] == 1;
                        res := true;
                    }
                    k := k + 1;
                }
                j := j + 1;
            }
        }
        i := i + 1;
    }
}
// </vc-code>

