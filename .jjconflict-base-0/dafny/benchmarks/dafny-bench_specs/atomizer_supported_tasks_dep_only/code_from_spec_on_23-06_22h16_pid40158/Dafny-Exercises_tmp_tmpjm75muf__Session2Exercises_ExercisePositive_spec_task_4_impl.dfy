// ATOM 
predicate positive(s:seq<int>)
{forall u::0<=u<|s| ==> s[u]>=0}

//ATOM_PLACEHOLDER_mpositive

//ATOM_PLACEHOLDER_mpositive3

//ATOM_PLACEHOLDER_mpositive4

//IMPL 
method mpositivertl(v:array<int>) returns (b:bool)
ensures b==positive(v[0..v.Length])
{
    b := true;
    var i := 0;
    while i < v.Length
        invariant 0 <= i <= v.Length
        invariant b == positive(v[0..i])
    {
        if v[i] < 0 {
            b := false;
            return;
        }
        i := i + 1;
    }
}