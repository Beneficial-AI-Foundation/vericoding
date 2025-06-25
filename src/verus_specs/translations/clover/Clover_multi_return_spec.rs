pub fn MultipleReturns(x: int, y: int) -> (more: int, less: int)
    ensures 
        more == x + y,
        less == x - y,
{
}