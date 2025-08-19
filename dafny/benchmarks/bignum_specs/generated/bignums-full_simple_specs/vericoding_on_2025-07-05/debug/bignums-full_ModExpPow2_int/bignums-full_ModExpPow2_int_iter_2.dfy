//ATOM

// computes res := x^y
opaque function Exp_int(x: nat, y:nat): nat
{
  if y == 0 then 1 else x * Exp_int(x, y - 1)
}

//IMPL 

// computes res := x^y % z when y == 2^n (repeated squaring)
method ModExpPow2_int(x: nat, y:nat, n:nat, z: nat) returns (res:nat)
  requires y == Exp_int(2, n)
  requires z > 0
  ensures res == Exp_int(x,y) % z
  decreases n
{
  if n == 0 {
    /* code modified by LLM (iteration 1): Fixed base case - when n=0, y=2^0=1, so x^y = x^1 = x */
    res := x % z;
  } else {
    /* code modified by LLM (iteration 1): Fixed recursive call arguments and added assertion to help verification */
    var temp := ModExpPow2_int(x, Exp_int(2, n-1), n-1, z);
    /* code modified by LLM (iteration 1): Added assertion to establish the mathematical relationship for repeated squaring */
    assert Exp_int(x, y) == Exp_int(Exp_int(x, Exp_int(2, n-1)), 2);
    /* code modified by LLM (iteration 1): Added assertion to show temp represents x^(2^(n-1)) % z */
    assert temp == Exp_int(x, Exp_int(2, n-1)) % z;
    res := (temp * temp) % z;
  }
}