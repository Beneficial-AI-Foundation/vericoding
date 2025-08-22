// ATOM 
predicate P(x: int)
// ATOM 

predicate Q(x: int)
// SPEC 

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
