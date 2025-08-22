// ATOM 
function Average (a: int, b: int): int 
{
    (a + b) / 2
}


//IMPL TripleConditions
method TripleConditions(x: int) returns (r: int) 
ensures r == 3 * x
{
    r := 3 * x;
}


//IMPL ProveSpecificationsEquivalent
method ProveSpecificationsEquivalent(x: int) {
}