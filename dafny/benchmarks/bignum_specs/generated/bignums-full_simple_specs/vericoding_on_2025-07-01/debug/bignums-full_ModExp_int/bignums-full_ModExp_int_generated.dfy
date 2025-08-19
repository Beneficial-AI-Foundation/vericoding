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
    if n == 0 {
        if y == 0 {
            res := 1 % z;
        } else {
            // y == 1 since y < Exp_int(2,1) = 2
            res := x % z;
        }
    } else {
        var pow2n := Exp_int(2, n);
        if y < pow2n {
            // y fits in n bits, recurse with n-1
            res := ModExp_int(x, y, n-1, z);
        } else {
            // y >= 2^n, so y = 2^n + remainder
            var remainder := y - pow2n;
            var pow_part := ModExpPow2_int(x, pow2n, n, z);
            var rem_part := ModExp_int(x, remainder, n-1, z);
            res := (pow_part * rem_part) % z;
        }
    }
}