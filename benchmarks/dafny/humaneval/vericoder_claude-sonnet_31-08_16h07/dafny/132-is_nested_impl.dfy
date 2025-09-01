

// <vc-helpers>
lemma NestedPatternExists(s: seq<int>, x: int, y: int, z: int, w: int)
    requires 0 <= x < y < z < w < |s|
    requires s[x] == 0 && s[y] == 0 && s[z] == 1 && s[w] == 1
    ensures exists a, b, c, d :: 0 <= a < b < c < d < |s| && s[a] == 0 && s[b] == 0 && s[c] == 1 && s[d] == 1
{
}
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
    
    while i < |s|
        invariant 0 <= i <= |s|
        invariant !res ==> forall x, y, z, w :: 0 <= x < y < z < w < |s| && x < i && s[x] == 0 && s[y] == 0 && s[z] == 1 && s[w] == 1 ==> false
    {
        if s[i] == 0 {
            var j := i + 1;
            while j < |s|
                invariant i + 1 <= j <= |s|
                invariant !res ==> forall y, z, w :: 0 <= i < y < z < w < |s| && y < j && s[i] == 0 && s[y] == 0 && s[z] == 1 && s[w] == 1 ==> false
            {
                if s[j] == 0 {
                    var k := j + 1;
                    while k < |s|
                        invariant j + 1 <= k <= |s|
                        invariant !res ==> forall z, w :: 0 <= i < j < z < w < |s| && z < k && s[i] == 0 && s[j] == 0 && s[z] == 1 && s[w] == 1 ==> false
                    {
                        if s[k] == 1 {
                            var l := k + 1;
                            while l < |s|
                                invariant k + 1 <= l <= |s|
                                invariant !res ==> forall w :: 0 <= i < j < k < w < |s| && w < l && s[i] == 0 && s[j] == 0 && s[k] == 1 && s[w] == 1 ==> false
                            {
                                if s[l] == 1 {
                                    NestedPatternExists(s, i, j, k, l);
                                    res := true;
                                    return;
                                }
                                l := l + 1;
                            }
                        }
                        k := k + 1;
                    }
                }
                j := j + 1;
            }
        }
        i := i + 1;
    }
}
// </vc-code>

