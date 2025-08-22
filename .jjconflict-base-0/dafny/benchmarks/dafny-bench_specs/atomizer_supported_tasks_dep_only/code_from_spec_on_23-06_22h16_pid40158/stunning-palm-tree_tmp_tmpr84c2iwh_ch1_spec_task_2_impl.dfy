// Ex 1.9
function Average (a: int, b: int): int {
  (a + b) / 2
}

// Ex 1.3
//IMPL 
method Triple'(x: int) returns (r: int)
  // spec 1: ensures Average(r, 3*x) == 3*x
  ensures Average(2*r, 6*x) == 6*x
{
  /* code modified by LLM (iteration 1): setting r := 3 * x satisfies the postcondition */
  r := 3 * x;
}

//IMPL 
method Caller() {
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