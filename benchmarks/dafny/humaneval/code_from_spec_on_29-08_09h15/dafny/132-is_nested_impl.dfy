

// <vc-helpers>
lemma NestedPatternExists(s: seq<int>, x: int, y: int, z: int, w: int)
    requires 0 <= x < y < z < w < |s|
    requires s[x] == 0 && s[y] == 0 && s[z] == 1 && s[w] == 1
    ensures exists a, b, c, d :: 0 <= a < b < c < d < |s| && s[a] == 0 && s[b] == 0 && s[c] == 1 && s[d] == 1
{
}

lemma NoNestedPatternHelper(s: seq<int>)
    requires forall x, y, z, w :: 0 <= x < y < z < w < |s| ==> !(s[x] == 0 && s[y] == 0 && s[z] == 1 && s[w] == 1)
    ensures !(exists x, y, z, w :: 0 <= x < y < z < w < |s| && s[x] == 0 && s[y] == 0 && s[z] == 1 && s[w] == 1)
{
}
// </vc-helpers>

// <vc-description>
/*
function_signature: def is_nested(string: str) -> Bool
Create a function that takes a string as input which contains only parentheses. The function should return True if and only if there is a valid subsequence of parentheses where at least one parenthesis in the subsequence is nested.
*/
// </vc-description>

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
        invariant !res ==> forall x, y, z, w :: 0 <= x < y < z < w < |s| && w < i ==> !(s[x] == 0 && s[y] == 0 && s[z] == 1 && s[w] == 1)
        invariant res ==> exists x, y, z, w :: 0 <= x < y < z < w < |s| && s[x] == 0 && s[y] == 0 && s[z] == 1 && s[w] == 1
    {
        if s[i] == 0 {
            var j := i + 1;
            while j < |s|
                invariant i < j <= |s|
                invariant !res ==> forall y, z, w :: i < y < z < w < |s| && w < j ==> !(s[i] == 0 && s[y] == 0 && s[z] == 1 && s[w] == 1)
                invariant res ==> exists x, y, z, w :: 0 <= x < y < z < w < |s| && s[x] == 0 && s[y] == 0 && s[z] == 1 && s[w] == 1
            {
                if s[j] == 0 {
                    var k := j + 1;
                    while k < |s|
                        invariant j < k <= |s|
                        invariant !res ==> forall z, w :: j < z < w < |s| && w < k ==> !(s[i] == 0 && s[j] == 0 && s[z] == 1 && s[w] == 1)
                        invariant res ==> exists x, y, z, w :: 0 <= x < y < z < w < |s| && s[x] == 0 && s[y] == 0 && s[z] == 1 && s[w] == 1
                    {
                        if s[k] == 1 {
                            var l := k + 1;
                            while l < |s|
                                invariant k < l <= |s|
                                invariant !res ==> forall w :: k < w < l ==> !(s[i] == 0 && s[j] == 0 && s[k] == 1 && s[w] == 1)
                                invariant res ==> exists x, y, z, w :: 0 <= x < y < z < w < |s| && s[x] == 0 && s[y] == 0 && s[z] == 1 && s[w] == 1
                            {
                                if s[l] == 1 {
                                    res := true;
                                    NestedPatternExists(s, i, j, k, l);
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
    NoNestedPatternHelper(s);
}
// </vc-code>

