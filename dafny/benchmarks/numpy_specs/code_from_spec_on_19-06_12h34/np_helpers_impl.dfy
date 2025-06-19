//ATOM
function Add(x: int, y: int): int
{
    x + y
}

//IMPL
method Double(x: int) returns (result: int)
requires x >= 0
ensures result == 2 * x
{
    /* code modified by LLM (iteration 1): Added implementation to satisfy postcondition */
    result := 2 * x;
}