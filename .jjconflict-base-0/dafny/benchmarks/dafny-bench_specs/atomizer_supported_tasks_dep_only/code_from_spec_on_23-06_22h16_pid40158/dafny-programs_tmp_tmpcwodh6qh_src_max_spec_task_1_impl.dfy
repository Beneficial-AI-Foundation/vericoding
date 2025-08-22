//IMPL Max
method Max(a: int, b: int) returns (c: int)
  ensures a >= b ==> c == a
  ensures b >= a ==> c == b
{
  /* code modified by LLM (iteration 1): removed duplicate method definition to fix compilation error */
  if a >= b {
    c := a;
  } else {
    c := b;
  }
}