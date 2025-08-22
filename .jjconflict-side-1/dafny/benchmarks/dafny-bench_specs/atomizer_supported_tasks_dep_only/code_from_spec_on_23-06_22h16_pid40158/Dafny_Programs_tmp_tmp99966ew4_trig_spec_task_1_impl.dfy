//ATOM 
predicate P(x: int)

//ATOM 
predicate Q(x: int)

//IMPL test
method test()
    requires forall x :: P(x) && Q(x)
    ensures Q(0)
{
    // The postcondition Q(0) follows directly from the precondition
    // since the precondition states that for all x, Q(x) holds
    // and 0 is a valid value for x
}