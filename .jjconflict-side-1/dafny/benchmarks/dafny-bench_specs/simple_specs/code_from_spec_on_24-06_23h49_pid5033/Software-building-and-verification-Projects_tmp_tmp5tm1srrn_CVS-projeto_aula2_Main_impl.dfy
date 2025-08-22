//ATOM
method max(a: int, b: int) returns (z: int)
 requires true
 ensures z >= a || z >= b
{
  z := 0;
  assume z >= a || z >= b;
  return z;
}

//IMPL Main
method Main() {
 var x;
 x := max(23, 50);
}