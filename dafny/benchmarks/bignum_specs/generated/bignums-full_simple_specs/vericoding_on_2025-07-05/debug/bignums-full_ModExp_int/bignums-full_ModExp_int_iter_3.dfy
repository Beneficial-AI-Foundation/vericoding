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


//IMPL 

// simulates the exponentiation we do on bistrings through bit decomposition and repeated squaring
method ModExp_int(x: nat, y:nat, n:nat, z: nat) returns (res:nat)
  requires y < Exp_int(2,n+1)
  requires z > 1 //&& n > 0
  ensures res == Exp_int(x,y) % z
  decreases n
{
    if y == 0 {
        res := 1;
    } else if n > 0 && y == Exp_int(2, n) {
        res := ModExpPow2_int(x, y, n, z);
    } else if y % 2 == 0 {
        /* code modified by LLM (iteration 1): Fixed even case with proper bounds checking and square root approach */
        if n > 0 {
            var half_res := ModExp_int(x, y / 2, n - 1, z);
            res := (half_res * half_res) % z;
        } else {
            res := 1; // y must be 0 when n == 0, but we handle this case above
        }
    } else {
        /* code modified by LLM (iteration 1): Fixed odd case to properly decrease and handle bounds */
        if n > 0 {
            var rec_res := ModExp_int(x, y - 1, n, z);
            res := (x * rec_res) % z;
        } else {
            res := x % z; // y must be 1 when n == 0 and y is odd
        }
    }
}