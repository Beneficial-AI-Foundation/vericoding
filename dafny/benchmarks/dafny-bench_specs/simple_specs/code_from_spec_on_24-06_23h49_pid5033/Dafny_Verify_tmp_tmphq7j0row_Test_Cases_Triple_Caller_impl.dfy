//ATOM

method TripleConditions(x: int) returns (r: int) 
requires x % 2 == 0
ensures r == 3 * x
{
  /* code modified by LLM (iteration 1): fixed syntax error in assume statement and corrected logic to satisfy postcondition */
  r := 3 * x;
}


//IMPL

method Caller() {
  /* code modified by LLM (iteration 1): added implementation that calls TripleConditions with valid input */
  var result := TripleConditions(4);
  assert result == 12;
}