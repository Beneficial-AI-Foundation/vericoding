// Ex 1.3
// SPEC 

pub fn Triple_prime(x: int) -> (r: int)
    ensures(Average(2*r, 6*x) == 6*x)
{
}

// SPEC 

pub fn Caller()
{
}

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
fn Average(a: int, b: int) -> int {
    (a + b) / 2
}

// SPEC 

pub fn Triple_prime(x: int) -> (r: int)
    ensures(Average(2*r, 6*x) == 6*x)
{
}