//ATOM
predicate allEqual(s:seq<int>)
{forall i,j::0<=i<|s| && 0<=j<|s| ==> s[i]==s[j] }

//IMPL mallEqual4
method mallEqual4(v:array<int>) returns (b:bool)
ensures b==allEqual(v[0..v.Length])
{
    if v.Length <= 1 {
        b := true;
    } else {
        b := true;
        var i := 1;
        while i < v.Length
            invariant 1 <= i <= v.Length
            invariant b == (forall k,l :: 0 <= k < i && 0 <= l < i ==> v[k] == v[l])
        {
            if v[i] != v[0] {
                b := false;
                break;
            }
            i := i + 1;
        }
    }
}