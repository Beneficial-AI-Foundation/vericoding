//IMPL sqrt
method sqrt(x: real) returns (r: real)
  requires x >= 0.0
  ensures r >= 0.0 && r * r == x
  ensures exists r :: r >= 0.0 && r * r == x
{
  /* code modified by LLM (iteration 4): Handle special case and use such-that with proper witness */
  if x == 0.0 {
    return 0.0;
  } else {
    // Use such-that to find a square root
    var sqrt_result :| sqrt_result >= 0.0 && sqrt_result * sqrt_result == x;
    return sqrt_result;
  }
}