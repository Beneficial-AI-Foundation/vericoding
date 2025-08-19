//IMPL RotateLeftBits
method RotateLeftBits(n: bv32, d: int) returns (result: bv32)
  requires 0 <= d < 32
  ensures result == ((n << d) | (n >> (32 - d)))
{
  /* code modified by LLM (iteration 1): removed non-Dafny explanatory text and kept only the implementation */
  result := (n << d) | (n >> (32 - d));
}