//ATOM

method Fact(x: int) returns (y: int)
 requires x >= 0;  
{
  y := 0;
  return y;
}


// SPEC
method Main() {
  var a := Fact(87);
  print a;
}
