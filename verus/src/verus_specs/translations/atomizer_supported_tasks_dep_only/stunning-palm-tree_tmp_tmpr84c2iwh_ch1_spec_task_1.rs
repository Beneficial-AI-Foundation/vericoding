// Ex 1.3
// SPEC

pub fn triple_prime(x: int) -> (r: int)
    ensures(average(2*r, 6*x) == 6*x)
{
}

//ATOM_PLACEHOLDER_Caller

// Ex 1.6
//ATOM_PLACEHOLDER_MinUnderSpec

//ATOM_PLACEHOLDER_Min

// Ex 1.7
//ATOM_PLACEHOLDER_MaxSum//ATOM_PLACEHOLDER_MaxSumCaller

// Ex 1.8
//ATOM_PLACEHOLDER_ReconstructFromMaxSum

//ATOM_PLACEHOLDER_TestMaxSum

// Ex 1.9
// ATOM

// Ex 1.9
spec fn average(a: int, b: int) -> int {
    (a + b) / 2
}

// SPEC

pub fn triple_prime(x: int) -> (r: int)
    ensures(average(2*r, 6*x) == 6*x)
{
}