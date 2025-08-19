//ATOM

method Forbid42(x:int, y:int) returns (z:int)
requires y != 42
ensures z == x/(42-y)
{
  /* code modified by LLM (iteration 1): Fixed syntax error - changed assume statement to proper assignment */
  z := x/(42-y);
  return z;
}


//ATOM

method Allow42(x:int, y:int) returns (z: int, err:bool) 
ensures y != 42 ==> z == x/(42-y) && err == false
ensures y == 42 ==> z == 0 && err == true
{
  /* code modified by LLM (iteration 1): Fixed implementation to properly handle both cases with conditional logic */
  if y == 42 {
    z := 0;
    err := true;
  } else {
    z := x/(42-y);
    err := false;
  }
  return z, err;
}


//IMPL TEST1

method TEST1()
{
}