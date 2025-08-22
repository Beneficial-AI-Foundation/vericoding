//IMPL m3
/* code modified by LLM (iteration 1): Fixed compilation error by moving ensures clause before method body and added implementation */
method m3(x: int, y: int) returns (z: bool)
  ensures z ==> x == y
{
  z := x == y;
}