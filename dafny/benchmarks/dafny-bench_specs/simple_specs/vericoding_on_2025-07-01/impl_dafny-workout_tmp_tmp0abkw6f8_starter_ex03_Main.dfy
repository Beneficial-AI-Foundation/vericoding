//ATOM
method Abs(x: int) returns (y: int)
	requires x == -1
	ensures 0 <= y
	ensures 0 <= x ==> y == x
	ensures x < 0 ==> y == -x
{
  y := 0;
  assume 0 <= y;
  assume 0 <= x ==> y == x;
  assume x < 0 ==> y == -x;
  return y;
}


//ATOM

method Abs2(x: real) returns (y: real)
	requires x == -0.5
	ensures 0.0 <= y
	ensures 0.0 <= x ==> y == x
	ensures x < 0.0 ==> y == -x
{
  y := 0.0;
  assume 0.0 <= y;
  assume 0.0 <= x ==> y == x;
  assume x < 0.0 ==> y == -x;
  return y;
}


//IMPL

method Main()
{
	var a := Abs(-1);
	var a2 := Abs2(-0.5);
}