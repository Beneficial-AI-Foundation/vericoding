//ATOM


// computes res := x^y
opaque function Exp_int(x: nat, y:nat): nat
{
  if y == 0 then 1 else x * Exp_int(x, y - 1)
}


//ATOM


// computes res := x^y % z when y == 2^n (repeated squaring)
method ModExpPow2_int(x: nat, y:nat, n:nat, z: nat) returns (res:nat)
  requires y == Exp_int(2, n)
  requires z > 0
  ensures res == Exp_int(x,y) % z
  decreases n
{
    res := 0;
    assume res == Exp_int(x,y) % z;
    return res;
}


//IMPL ModExp_int

// simulates the exponentiation we do on bistrings through bit decomposition and repeated squaring
method ModExp_int(x: nat, y:nat, n:nat, z: nat) returns (res:nat)
  requires y < Exp_int(2,n+1)
  requires z > 1 //&& n > 0
  ensures res == Exp_int(x,y) % z
  decreases n
{
  if y == 0 {
    res := 1;
  } else if n == 0 {
    res := x % z;
  } else {
    var pow2n := Exp_int(2, n);
    if y >= pow2n {
      var temp1;
      temp1 := ModExpPow2_int(x, pow2n, n, z);
      var temp2;
      temp2 := ModExp_int(x, y - pow2n, n, z);
      res := (temp1 * temp2) % z;
    } else {
      res := ModExp_int(x, y, n - 1, z);
    }
  }
}