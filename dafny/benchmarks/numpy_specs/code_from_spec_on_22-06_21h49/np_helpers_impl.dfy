//IMPL ExampleMethod
method Add(x: int, y: int) returns (result: int)
  requires x >= 0 && y >= 0
  ensures result == x + y
{
  /* code modified by LLM (iteration 1): added implementation to satisfy postcondition */
  result := x + y;
}