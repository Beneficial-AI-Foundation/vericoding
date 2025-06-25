// ATOM 
spec fn P(x: int) -> bool;
//ATOM_PLACEHOLDER_Q// SPEC 

pub fn test()
    requires(forall|x: int| P(x) && Q(x))
    ensures(Q(0))
{
}