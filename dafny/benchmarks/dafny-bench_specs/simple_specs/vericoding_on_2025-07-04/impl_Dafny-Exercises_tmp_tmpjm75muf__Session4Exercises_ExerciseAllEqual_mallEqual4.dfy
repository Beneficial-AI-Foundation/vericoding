//ATOM
predicate allEqual(s:seq<int>)
{forall i,j::0<=i<|s| && 0<=j<|s| ==> s[i]==s[j] }

//IMPL 
method mallEqual4(v:array<int>) returns (b:bool)
ensures b==allEqual(v[0..v.Length])
{
    if v.Length == 0 {
        b := true;
        return;
    }
    
    var i := 1;
    while i < v.Length
        invariant 1 <= i <= v.Length
        invariant forall k :: 0 <= k < i ==> v[k] == v[0]
    {
        if v[i] != v[0] {
            b := false;
            return;
        }
        i := i + 1;
    }
    b := true;
}