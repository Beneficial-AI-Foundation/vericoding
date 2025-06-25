// ATOM 
spec fn P(x: int) -> bool;
// ATOM 

spec fn Q(x: int) -> bool;
// SPEC 

pub fn test()
    requires(forall|x: int| P(x) && Q(x))
    ensures(Q(0))
{
}