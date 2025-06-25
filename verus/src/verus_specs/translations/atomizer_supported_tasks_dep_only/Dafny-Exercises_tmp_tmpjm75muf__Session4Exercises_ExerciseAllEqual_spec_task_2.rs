// ATOM 
spec fn allEqual(s: Seq<int>) -> bool
{ forall|i: int, j: int| 0 <= i < s.len() && 0 <= j < s.len() ==> s[i] == s[j] }

//{forall|i: int, j: int| 0 <= i <= j < s.len() ==> s[i] == s[j] }
//{forall|i: int| 0 < i < s.len() ==> s[i-1] == s[i]} 
//{forall|i: int| 0 <= i < s.len()-1 ==> s[i] == s[i+1]}


//Ordered indexes
//ATOM_PLACEHOLDER_equivalenceNoOrder

//All equal to first
//ATOM_PLACEHOLDER_equivalenceEqualtoFirst



//ATOM_PLACEHOLDER_equivalenceContiguous



//ATOM_PLACEHOLDER_mallEqual1

// SPEC 

pub fn mallEqual2(v: &[int]) -> (b: bool)
    ensures(b == allEqual(v@.subrange(0, v@.len() as int)))
{
}




//ATOM_PLACEHOLDER_mallEqual3


//ATOM_PLACEHOLDER_mallEqual4


//ATOM_PLACEHOLDER_mallEqual5