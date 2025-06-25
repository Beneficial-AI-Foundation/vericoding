//ATOM

method Forbid42(x:int, y:int) returns (z:int)
requires y != 42
ensures z == x/(42-y)
{
  z := 0;
  assume z == x/(42-y);
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


//IMPL TEST1

method TEST1()
{
  // Simple implementation - no requires/ensures clauses to satisfy
  var result1, error1 := Allow42(10, 2);
  var result2, error2 := Allow42(10, 42);
}