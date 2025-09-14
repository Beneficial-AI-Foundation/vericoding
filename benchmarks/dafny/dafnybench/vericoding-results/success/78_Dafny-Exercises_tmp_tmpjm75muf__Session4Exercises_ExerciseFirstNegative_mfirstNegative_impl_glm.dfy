predicate positive(s:seq<int>)
{forall u::0<=u<|s| ==> s[u]>=0}

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method mfirstNegative(v:array<int>) returns (b:bool, i:int)
ensures b <==> exists k::0<=k<v.Length && v[k]<0
ensures b ==> 0<=i<v.Length && v[i]<0 && positive(v[0..i])
// </vc-spec>
// <vc-code>
{
    var n := v.Length;
    i := 0;
    while i < n
        invariant 0 <= i <= n
        invariant forall j :: 0 <= j < i ==> v[j] >= 0
    {
        if v[i] < 0 {
            return true, i;
        } else {
            i := i + 1;
        }
    }
    return false, 0;
}
// </vc-code>

