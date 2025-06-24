// ATOM 
predicate positive(s:seq<int>)
{forall u::0<=u<|s| ==> s[u]>=0}



// SPEC 


method mpositive(v:array<int>) returns (b:bool)
ensures b==positive(v[0..v.Length])
{
}


// SPEC 


method mpositive(v:array<int>) returns (b:bool)
ensures b==positive(v[0..v.Length])
{
}
3

// SPEC 


method mpositive(v:array<int>) returns (b:bool)
ensures b==positive(v[0..v.Length])
{
}
4

// SPEC 


method mpositive(v:array<int>) returns (b:bool)
ensures b==positive(v[0..v.Length])
{
}
rtl







