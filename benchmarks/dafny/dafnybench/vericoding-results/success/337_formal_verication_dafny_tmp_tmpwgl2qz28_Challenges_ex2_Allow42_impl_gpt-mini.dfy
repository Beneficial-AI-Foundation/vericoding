/*
    i)  Write a verified method with signature

// <vc-helpers>
// no helpers required
// </vc-helpers>

// <vc-spec>
method Allow42(x:int, y:int) returns (z: int, err:bool) 
ensures y != 42 ==> z == x/(42-y) && err == false;
ensures y == 42 ==> z == 0 && err == true;
// </vc-spec>
// <vc-code>
{
  if y == 42 {
    z := 0;
    err := true;
  } else {
    var denom := 42 - y;
    z := x / denom;
    err := false;
  }
}
// </vc-code>

