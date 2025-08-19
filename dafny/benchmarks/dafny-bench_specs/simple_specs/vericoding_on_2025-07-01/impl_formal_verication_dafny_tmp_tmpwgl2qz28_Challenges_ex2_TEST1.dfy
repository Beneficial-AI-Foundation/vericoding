//ATOM

method Forbid42(x:int, y:int) returns (z:int)
requires y != 42
ensures z == x/(42-y)
{
  z := 0;
  assume z ==> x/(42-y);
  return z;
}

//ATOM

method Allow42(x:int, y:int) returns (z: int, err:bool) 
ensures y != 42 ==> z == x/(42-y) && err == false
ensures y == 42 ==> z == 0 && err == true
{
  z := 0;
  err := false;
  assume y != 42 ==> z == x/(42-y) && err == false;
  assume y == 42 ==> z == 0 && err == true;
  return z, err;
}


// SPEC

method TEST1()
{
}