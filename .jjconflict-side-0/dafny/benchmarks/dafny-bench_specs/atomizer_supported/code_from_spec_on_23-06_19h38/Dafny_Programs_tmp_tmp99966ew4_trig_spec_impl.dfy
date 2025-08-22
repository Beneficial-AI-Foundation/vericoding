// ATOM 
predicate P(x: int)

// ATOM 
predicate Q(x: int)

// IMPL test
method test()
    requires forall x :: P(x) && Q(x)
    ensures Q(0)
{
    // The precondition states that for all x, both P(x) and Q(x) hold
    // Since this is true for all x, it's specifically true for x = 0
    // Therefore Q(0) holds, satisfying the postcondition
}