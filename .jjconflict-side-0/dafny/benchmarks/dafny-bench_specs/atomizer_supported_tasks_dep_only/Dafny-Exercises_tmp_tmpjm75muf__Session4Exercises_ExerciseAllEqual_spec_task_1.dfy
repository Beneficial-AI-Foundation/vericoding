// ATOM 
predicate allEqual(s:seq<int>)
{forall i,j::0<=i<|s| && 0<=j<|s| ==> s[i]==s[j] }

//{forall i,j::0<=i<=j<|s| ==> s[i]==s[j] }
//{forall i::0<i<|s| ==> s[i-1]==s[i]} 
//{forall i::0<=i<|s|-1 ==> s[i]==s[i+1]}


//Ordered indexes
//ATOM_PLACEHOLDER_equivalenceNoOrder

//All equal to first
//ATOM_PLACEHOLDER_equivalenceEqualtoFirst



//ATOM_PLACEHOLDER_equivalenceContiguous



// SPEC 



method mallEqual1(v:array<int>) returns (b:bool)
ensures b==allEqual(v[0..v.Length])
{
}


//ATOM_PLACEHOLDER_mallEqual2



//ATOM_PLACEHOLDER_mallEqual3


//ATOM_PLACEHOLDER_mallEqual4


//ATOM_PLACEHOLDER_mallEqual5









