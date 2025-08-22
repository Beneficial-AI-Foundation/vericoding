
// ATOM 

predicate positive(s:seq<int>)
{forall u::0<=u<|s| ==> s[u]>=0}


//ATOM_PLACEHOLDER_isEven

// ATOM 

function CountEven(s:seq<int>):int
requires positive(s)
{if s==[] then 0
 else (if (s[|s|-1]%2==0) then 1 else 0)+CountEven(s[..|s|-1])
 }


//ATOM_PLACEHOLDER_ArrayFacts

// SPEC 

method mcountEven(v:array<int>) returns (n:int)
requires positive(v[..])
ensures  n==CountEven(v[..])
{
}








