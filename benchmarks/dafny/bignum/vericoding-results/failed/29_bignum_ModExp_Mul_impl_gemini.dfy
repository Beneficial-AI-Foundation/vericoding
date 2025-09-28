// <vc-preamble>
ghost function Str2Int(s: string): nat
  requires ValidBitString(s)
  decreases s
{
  if |s| == 0 then  0  else  (2 * Str2Int(s[0..|s|-1]) + (if s[|s|-1] == '1' then 1 else 0))
}
ghost function Exp_int(x: nat, y:nat): nat
{
  if y == 0 then 1 else x * Exp_int(x, y - 1)
}
predicate ValidBitString(s: string)
{

  forall i | 0 <= i < |s| :: s[i] == '0' || s[i] == '1'
}

method Mul(s1: string, s2: string) returns (res: string)
  requires ValidBitString(s1) && ValidBitString(s2)
  ensures ValidBitString(res)
  ensures Str2Int(res) == Str2Int(s1) * Str2Int(s2)
{
  assume{:axiom} false;
}
// </vc-preamble>

// <vc-helpers>
lemma Str2IntProps(s: string)
    requires ValidBitString(s) && |s| > 0
    ensures Str2Int(s) == 2 * Str2Int(s[..|s|-1]) + (if s[|s|-1] == '1' then 1 else 0)
{
}

/* helper modified by LLM (iteration 9): [Fixed compilation error in NatToString by using 'let...in' expression.] */
function NatToString(n: nat): (s: string)
  ensures ValidBitString(s)
  ensures Str2Int(s) == n
  decreases n
{
    if n == 0 then "0"
    else
        let s_rest := NatToString(n / 2) in
        let bit := if n % 2 == 1 then "1" else "0" in
        if s_rest == "0" then bit else s_rest + bit
}

/* helper modified by LLM (iteration 5): [Added lemma for modular multiplication.] */
lemma lemma_mul_mod(a: nat, b: nat, n: nat)
  requires n > 0
  ensures (a * b) % n == ((a % n) * (b % n)) % n
{
}

/* helper modified by LLM (iteration 5): [Added lemma for properties of exponentiation.] */
lemma lemma_exp_add(x: nat, a: nat, b: nat)
  ensures Exp_int(x, a + b) == Exp_int(x, a) * Exp_int(x, b)
  decreases b
{
  if b > 0 {
    lemma_exp_add(x, a, b - 1);
  }
}
// </vc-helpers>

// <vc-spec>
method ModExp(sx: string, sy: string, sz: string) returns (res: string)
  requires ValidBitString(sx) && ValidBitString(sy) &&  ValidBitString(sz)
  ensures ValidBitString(res)
  ensures Str2Int(res) == Exp_int(Str2Int(sx), Str2Int(sy)) % Str2Int(sz)

  requires |sy| > 0 && Str2Int(sz) > 1
  decreases |sy|
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 9): [No change; the fix was for a compilation error in a helper function.] */
  if |sy| == 1 {
    if sy[0] == '0' { 
       res := "1";
    } else { 
       var x := Str2Int(sx);
       var z := Str2Int(sz);
       var r_nat := x % z;
       res := NatToString(r_nat);
    }
  } else {
    var sy_rest := sy[0..|sy|-1];
    var last_bit := sy[|sy|-1];

    var temp_res_s := ModExp(sx, sy_rest, sz);

    Str2IntProps(sy);
    
    var x := Str2Int(sx);
    var z := Str2Int(sz);
    var y_rest_n := Str2Int(sy_rest);
    
    var temp_res_n := Str2Int(temp_res_s);
    
    lemma_exp_add(x, y_rest_n, y_rest_n);
    lemma_mul_mod(Exp_int(x, y_rest_n), Exp_int(x, y_rest_n), z);

    var squared_n := (temp_res_n * temp_res_n) % z;
    
    if last_bit == '0' {
      res := NatToString(squared_n);
    } else {
      var x_mod_z := x % z;
      
      lemma_exp_add(x, 1, 2 * y_rest_n);
      lemma_mul_mod(x, Exp_int(x, 2 * y_rest_n), z);

      var final_res_n := (x_mod_z * squared_n) % z;
      res := NatToString(final_res_n);
    }
  }
}
// </vc-code>
