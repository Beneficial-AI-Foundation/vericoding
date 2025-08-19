//ATOM
method TripleConditions(x: int) returns (r: int) 
requires x % 2 == 0
ensures r == 3 * x
{
  /* code modified by LLM (iteration 1): Fixed compilation error - replaced invalid implication with correct assignment */
  r := 3 * x;
}

//IMPL 
method Caller() {
  /* code modified by LLM (iteration 1): Added call to TripleConditions to demonstrate usage */
  var result := TripleConditions(4);
  assert result == 12;
}