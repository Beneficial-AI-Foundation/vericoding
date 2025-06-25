pub fn Triple(x: int) -> (r: int)
{
}

pub fn TripleIf(x: int) -> (r: int) 
{
}

pub fn TripleOver(x: int) -> (r: int) 
{
}

pub fn TripleConditions(x: int) -> (r: int)
    requires(x % 2 == 0)
    ensures(r == 3 * x)
{
}

pub fn Caller() 
{
}