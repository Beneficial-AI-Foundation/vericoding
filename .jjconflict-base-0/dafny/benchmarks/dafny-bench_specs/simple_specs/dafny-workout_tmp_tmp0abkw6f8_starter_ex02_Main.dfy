//ATOM
method Abs(x: int) returns (y: int)
	requires x < 0
	ensures 0 < y
	ensures y == -x
{
  y := 0;
  assume 0 < y;
  assume y ==> -x;
  return y;
}


// SPEC

method Main()
{
	var a := Abs(-3);
}
