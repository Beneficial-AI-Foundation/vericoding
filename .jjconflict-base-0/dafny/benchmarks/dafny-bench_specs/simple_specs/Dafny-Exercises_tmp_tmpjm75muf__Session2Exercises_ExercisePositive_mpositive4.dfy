//ATOM
predicate positive(s:seq<int>)
{forall u::0<=u<|s| ==> s[u]>=0}


// SPEC

method mpositive4(v:array<int>) returns (b:bool)
ensures b==positive(v[0..v.Length])
{
}
