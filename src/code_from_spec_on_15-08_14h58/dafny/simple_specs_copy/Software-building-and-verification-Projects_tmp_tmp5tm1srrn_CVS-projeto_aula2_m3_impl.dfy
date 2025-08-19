//IMPL 
method m3(x: int,y: int) returns (z: bool)
 ensures z ==> x==y
{
  z := x == y;
}