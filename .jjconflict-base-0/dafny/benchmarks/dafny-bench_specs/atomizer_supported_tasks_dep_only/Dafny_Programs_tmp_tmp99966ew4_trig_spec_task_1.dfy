// ATOM 
predicate P(x: int)
//ATOM_PLACEHOLDER_Q// SPEC 

method test()
    requires forall x {
}
    ensures Q(0)
{
}
 :: P(x) && Q(x)
    ensures Q(0)
{
}
 :: P(x) && Q(x)
    ensures Q(0)
{
}
