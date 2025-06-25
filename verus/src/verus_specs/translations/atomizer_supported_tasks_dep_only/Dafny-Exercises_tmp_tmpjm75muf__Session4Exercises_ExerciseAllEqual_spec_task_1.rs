// ATOM 
spec fn allEqual(s: Seq<int>) -> bool
{
    forall|i: int, j: int| 0 <= i < s.len() && 0 <= j < s.len() ==> s[i] == s[j]
}

//{forall i,j::0<=i<=j<|s| ==> s[i]==s[j] }
//{forall i::0<i<|s| ==> s[i-1]==s[i]} 
//{forall i::0<=i<|s|-1 ==> s[i]==s[i+1]}


//Ordered indexes
//ATOM_PLACEHOLDER_equivalenceNoOrder

//All equal to first
//ATOM_PLACEHOLDER_equivalenceEqualtoFirst



//ATOM_PLACEHOLDER_equivalenceContiguous



// SPEC 



pub fn mallEqual1(v: &[int]) -> (b: bool)
    ensures(b == allEqual(v@))
{
}


//ATOM_PLACEHOLDER_mallEqual2



//ATOM_PLACEHOLDER_mallEqual3


//ATOM_PLACEHOLDER_mallEqual4


//ATOM_PLACEHOLDER_mallEqual5