//IMPL
/* code modified by LLM (iteration 1): removed invalid text at beginning of file that was causing parse error */
method NthDecagonalNumber(n: int) returns (decagonal: int)
  requires n >= 0
  ensures decagonal == 4 * n * n - 3 * n
{
  decagonal := 4 * n * n - 3 * n;
}