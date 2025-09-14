predicate positive(s:seq<int>)
{forall u::0<=u<|s| ==> s[u]>=0}

// <vc-helpers>
predicate allNonNegative(s:seq<int>)
{forall u::0<=u<|s| ==> s[u]>=0}
// </vc-helpers>

// <vc-spec>
method mfirstNegative(v:array<int>) returns (b:bool, i:int)
ensures b <==> exists k::0<=k<v.Length && v[k]<0
ensures b ==> 0<=i<v.Length && v[i]<0 && positive(v[0..i])
// </vc-spec>
// <vc-code>
{
    var k := 0;
    while k < v.Length
        invariant 0 <= k <= v.Length
        invariant allNonNegative(v[0..k])
    {
        if v[k] < 0 {
            return true, k;
        }
        k := k + 1;
    }
    return false, 0;
}
// </vc-code>

