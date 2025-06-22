/* code modified by LLM (iteration 1): Fixed syntax error by moving ensures clause before method body and added implementation */
method Multiply(a: int, b: int) returns (result: int)
  ensures result == a * b
{
  result := a * b;
}