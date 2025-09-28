// <vc-preamble>
ghost function Exp_int(x: nat, y:nat): nat
{
  if y == 0 then 1 else x * Exp_int(x, y - 1)
}
predicate ValidBitString(s: string)
{

  forall i | 0 <= i < |s| :: s[i] == '0' || s[i] == '1'
}
ghost function Str2Int(s: string): nat
  requires ValidBitString(s)
  decreases s
{
  if |s| == 0 then  0  else  (2 * Str2Int(s[0..|s|-1]) + (if s[|s|-1] == '1' then 1 else 0))
}

method DivMod(dividend: string, divisor: string) returns (quotient: string, remainder: string)
  requires ValidBitString(dividend) && ValidBitString(divisor)
  requires Str2Int(divisor) > 0
  ensures ValidBitString(quotient) && ValidBitString(remainder)
  ensures Str2Int(quotient) == Str2Int(dividend) / Str2Int(divisor)
  ensures Str2Int(remainder) == Str2Int(dividend) % Str2Int(divisor)
{
  assume{:axiom} false;
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
/* helper modified by LLM (iteration 4): Added lemma for modular multiplication property. */
lemma LemmaModMul(a: nat, b: nat, m: nat)
    requires m > 0
    ensures (a * b) % m == ((a % m) * (b % m)) % m
{
}

/* helper modified by LLM (iteration 4): Added lemma for exponentiation property. */
lemma LemmaExpAdd(x: nat, y: nat, z: nat)
  ensures Exp_int(x, y + z) == Exp_int(x, y) * Exp_int(x, z)
  decreases z
{
  if z > 0 {
    LemmaExpAdd(x, y, z - 1);
  }
}

/* helper modified by LLM (iteration 2): Added helper function to generate the string representation of 2^n. */
function pow2_string(n: nat): (s: string)
    ensures ValidBitString(s)
    ensures |s| == n + 1
    ensures Str2Int(s) == Exp_int(2, n)
    decreases n
{
    if n == 0 then "1"
    else pow2_string(n - 1) + "0"
}
// </vc-helpers>

// <vc-spec>
method ModExpPow2(sx: string, sy: string, n: nat, sz: string) returns (res: string)
  requires ValidBitString(sx) && ValidBitString(sy) &&  ValidBitString(sz)

  requires Str2Int(sy) == Exp_int(2,n) || Str2Int(sy) == 0
  requires |sy| == n+1
  requires Str2Int(sz) > 1
  ensures ValidBitString(res)
  ensures Str2Int(res) == Exp_int(Str2Int(sx), Str2Int(sy)) % Str2Int(sz)
  decreases n
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 4): Invoking lemmas to bridge verifier's logical gaps. */
  if sy[0] == '0' {
    assert Str2Int(sy) == 0;
    res := "1";
  } else {
    assert Str2Int(sy) == Exp_int(2,n);
    if n == 0 {
      assert Str2Int(sy) == 1;
      var _, rem := DivMod(sx, sz);
      res := rem;
    } else {
      var s_half_y := pow2_string(n - 1);
      var temp_res := ModExpPow2(sx, s_half_y, n - 1, sz);
      var squared := Mul(temp_res, temp_res);
      var _, final_rem := DivMod(squared, sz);
      
      var x_int := Str2Int(sx);
      var y_half_int := Exp_int(2, n-1);
      var z_int := Str2Int(sz);

      LemmaModMul(Exp_int(x_int, y_half_int), Exp_int(x_int, y_half_int), z_int);
      LemmaExpAdd(x_int, y_half_int, y_half_int);
      assert Str2Int(sy) == y_half_int + y_half_int;

      res := final_rem;
    }
  }
}

// </vc-code>
