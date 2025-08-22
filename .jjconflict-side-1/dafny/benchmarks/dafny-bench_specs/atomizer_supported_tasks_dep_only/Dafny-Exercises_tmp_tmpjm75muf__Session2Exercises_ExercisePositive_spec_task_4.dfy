// ATOM 
predicate positive(s:seq<int>)
{forall u::0<=u<|s| ==> s[u]>=0}



//ATOM_PLACEHOLDER_mpositive

//ATOM_PLACEHOLDER_mpositive3

//ATOM_PLACEHOLDER_mpositive4

// SPEC 

method mpositivertl(v:array<int>) returns (b:bool)
ensures b==positive(v[0..v.Length])
{
}








