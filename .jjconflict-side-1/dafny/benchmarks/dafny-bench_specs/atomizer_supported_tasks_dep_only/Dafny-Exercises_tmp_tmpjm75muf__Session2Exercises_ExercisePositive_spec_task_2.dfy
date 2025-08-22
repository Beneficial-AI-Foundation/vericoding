// ATOM 
predicate positive(s:seq<int>)
{forall u::0<=u<|s| ==> s[u]>=0}



//ATOM_PLACEHOLDER_mpositive

// SPEC 

method mpositive3(v:array<int>) returns (b:bool)
ensures b==positive(v[0..v.Length])
{
}


//ATOM_PLACEHOLDER_mpositive4

//ATOM_PLACEHOLDER_mpositivertl







