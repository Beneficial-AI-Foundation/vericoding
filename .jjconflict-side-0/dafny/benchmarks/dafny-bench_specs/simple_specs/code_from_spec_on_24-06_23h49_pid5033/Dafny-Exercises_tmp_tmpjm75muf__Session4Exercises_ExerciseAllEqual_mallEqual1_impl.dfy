//ATOM
predicate allEqual(s:seq<int>)
{forall i,j::0<=i<|s| && 0<=j<|s| ==> s[i]==s[j] }

//IMPL mallEqual1
method mallEqual1(v:array<int>) returns (b:bool)
ensures b==allEqual(v[0..v.Length])
{
    if v.Length <= 1 {
        b := true;
    } else {
        var i := 1;
        b := true;
        while i < v.Length
            invariant 1 <= i <= v.Length
            invariant b == (forall k :: 0 <= k < i ==> v[k] == v[0])
        {
            if v[i] != v[0] {
                b := false;
                return;
            }
            i := i + 1;
        }
    }
}