//ATOM
predicate allEqual(s:seq<int>)
{forall i,j::0<=i<|s| && 0<=j<|s| ==> s[i]==s[j] }

//IMPL
method mallEqual3(v:array<int>) returns (b:bool)
ensures b==allEqual(v[0..v.Length])
{
    if v.Length <= 1 {
        b := true;
        return;
    }
    
    var i := 1;
    while i < v.Length
        invariant 1 <= i <= v.Length
        invariant forall k,j :: 0 <= k < i && 0 <= j < i ==> v[k] == v[j]
    {
        if v[i] != v[0] {
            b := false;
            return;
        }
        i := i + 1;
    }
    b := true;
}