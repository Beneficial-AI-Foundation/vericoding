//ATOM

// Ex 1.9
function Average (a: int, b: int): int {
 (a + b) / 2
}


// SPEC

method Triple'(x: int) returns (r: int)
 // spec 1: ensures Average(r, 3*x) == 3*x
 ensures Average(2*r, 6*x) == 6*x
{
}