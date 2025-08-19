predicate P(x: int)
{
    true
}

//IMPL 
method test(y: int)
    requires forall x :: P(x)
{
}