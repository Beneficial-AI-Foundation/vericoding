//ATOM

method Fact(x: int) returns (y: int)
 /* code modified by LLM (iteration 1): removed unnecessary semicolon after requires clause */
 requires x >= 0
{
  y := 0;
  return y;
}


//IMPL
method Main() {
  var a := Fact(87);
  print a;
}