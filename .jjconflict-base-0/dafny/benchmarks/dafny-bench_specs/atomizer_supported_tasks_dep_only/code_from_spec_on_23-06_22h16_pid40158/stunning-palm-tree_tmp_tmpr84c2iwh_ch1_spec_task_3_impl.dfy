// Ex 1.3
//ATOM_PLACEHOLDER_Triple

//ATOM_PLACEHOLDER_Caller

// Ex 1.6
// SPEC 

// Ex 1.6
//IMPL MinUnderSpec
method MinUnderSpec (x: int, y: int) returns (r: int)
  ensures r <= x && r <= y 
{
  if x <= y {
    r := x;
  } else {
    r := y;
  }
}

//ATOM_PLACEHOLDER_Min

// Ex 1.7
//ATOM_PLACEHOLDER_MaxSum//ATOM_PLACEHOLDER_MaxSumCaller

// Ex 1.8
//ATOM_PLACEHOLDER_ReconstructFromMaxSum

//ATOM_PLACEHOLDER_TestMaxSum

// Ex 1.9
//ATOM_PLACEHOLDER_Average

//ATOM_PLACEHOLDER_Triple'