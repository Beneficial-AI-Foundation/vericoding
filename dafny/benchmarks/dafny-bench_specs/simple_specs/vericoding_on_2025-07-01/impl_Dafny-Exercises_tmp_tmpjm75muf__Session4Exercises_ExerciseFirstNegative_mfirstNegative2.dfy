//ATOM
predicate positive(s:seq<int>)
{forall u::0<=u<|s| ==> s[u]>=0}

//IMPL
method mfirstNegative2(v:array<int>) returns (b:bool, i:int)
ensures b <==> exists k::0<=k<v.Length && v[k]<0
ensures b ==> 0<=i<v.Length && v[i]<0 && positive(v[0..i])
{
    i := 0;
    while i < v.Length
        invariant 0 <= i <= v.Length
        invariant positive(v[0..i])
    {
        if v[i] < 0 {
            b := true;
            return;
        }
        i := i + 1;
    }
    b := false;
}