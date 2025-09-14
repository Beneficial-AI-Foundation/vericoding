ghost function Exp_int(x: nat, y:nat): nat
{
  if y == 0 then 1 else x * Exp_int(x, y - 1)
}
predicate ValidBitString(s: string)
{
  // All characters must be '0' or '1'.
  forall i | 0 <= i < |s| :: s[i] == '0' || s[i] == '1'
}
ghost function Str2Int(s: string): nat
  requires ValidBitString(s)
  decreases s
{
  if |s| == 0 then  0  else  (2 * Str2Int(s[0..|s|-1]) + (if s[|s|-1] == '1' then 1 else 0))
}

method Add(s1: string, s2: string) returns (res: string)
  requires ValidBitString(s1) && ValidBitString(s2)
  ensures ValidBitString(res)
  ensures Str2Int(res) == Str2Int(s1) + Str2Int(s2)
{
  assume{:axiom} false;
}

// <vc-helpers>
lemma ExpLemma(x: nat, y: nat)
  ensures Exp_int(x, y) == (if y == 0 then 1 else x * Exp_int(x, y-1))
{
}

lemma ModExpLemma(base: nat, exp: nat, divisor: nat)
  requires divisor > 1
  ensures Exp_int(base, exp) % divisor == (if exp == 0 then 1 % divisor else (base * (Exp_int(base, exp-1) % divisor)) % divisor) % divisor
{
  if exp > 0 {
    var inner := Exp_int(base, exp-1) % divisor;
    assert Exp_int(base, exp) % divisor == (base * Exp_int(base, exp-1)) % divisor;
    assert (base * Exp_int(base, exp-1)) % divisor == (base * inner) % divisor;
  }
}

lemma Exp2Lemma(n: nat)
  ensures Exp_int(2, n) == (if n == 0 then 1 else 2 * Exp_int(2, n-1))
{
}

lemma Exp2Zero()
  ensures Exp_int(2, 0) == 1
{
}

lemma Str2IntZero(s: string)
  requires ValidBitString(s)
  requires |s| == 1
  requires s[0] == '0'
  ensures Str2Int(s) == 0
{
}

lemma Str2IntOne(s: string)
  requires ValidBitString(s)
  requires |s| == 1
  requires s[0] == '1'
  ensures Str2Int(s) == 1
{
}

lemma ModuloOne(x: nat, m: nat)
  requires m > 1
  ensures 1 % m == 1
{
}

ghost function BinaryResult(res_val: nat): string
  requires res_val == 0 || res_val == 1
{
  if res_val == 0 then "0" else "1"
}

lemma Str2IntLemma(s: string)
  requires ValidBitString(s)
  ensures |s| > 0 ==> Str2Int(s) == 2 * Str2Int(s[0..|s|-1]) + (if s[|s|-1] == '1' then 1 else 0)
{
}

lemma Str2IntLengthLemma(s: string, n: nat)
  requires ValidBitString(s)
  requires |s| == n+1
  requires Str2Int(s) == Exp_int(2, n) || Str2Int(s) == 0
  ensures Str2Int(s[0..|s|-1]) == (if s[|s|-1] == '1' then Exp_int(2, n-1) else 0)
{
  Str2IntLemma(s);
  if s[|s|-1] == '1' {
    assert Str2Int(s) == 2 * Str2Int(s[0..|s|-1]) + 1;
  } else {
    assert Str2Int(s) == 2 * Str2Int(s[0..|s|-1]);
  }
}

lemma ExpIntSquared(base: nat, power: nat)
  ensures Exp_int(base, 2 * power) == Exp_int(base, power) * Exp_int(base, power)
{
}

lemma ExpIntPlusOne(base: nat, power: nat)
  ensures Exp_int(base, 2 * power + 1) == base * Exp_int(base, power) * Exp_int(base, power)
{
}

function method IntToBitString(n: nat): string
  requires n == 0 || n == 1
{
  if n == 0 then "0" else "1"
}
// </vc-helpers>
// </vc-helpers>

// <vc-spec>
method ModExpPow2(sx: string, sy: string, n: nat, sz: string) returns (res: string)
  requires ValidBitString(sx) && ValidBitString(sy) &&  ValidBitString(sz)
  // sy is power of 2 or zero
  requires Str2Int(sy) == Exp_int(2,n) || Str2Int(sy) == 0
  requires |sy| == n+1
  requires Str2Int(sz) > 1
  ensures ValidBitString(res)
  ensures Str2Int(res) == Exp_int(Str2Int(sx), Str2Int(sy)) % Str2Int(sz)
  decreases n
// </vc-spec>
// <vc-code>
{
  if n == 0 {
    if sy[0] == '1' {
      assert |sy| == 1;
      assert Str2Int(sy) == 1;
      var base := Str2Int(sx);
      var divisor := Str2Int(sz);
      var result_val := base % divisor;
      res := IntToBitString(result_val);
      assert Exp_int(Str2Int(sx), Str2Int(sy)) == Exp_int(base, 1) == base;
      assert result_val == base % divisor;
    } else {
      assert |sy| == 1;
      assert Str2Int(sy) == 0;
      var divisor := Str2Int(sz);
      var result_val := 1 % divisor;
      res := IntToBitString(result_val);
      assert Exp_int(Str2Int(sx), Str2Int(sy)) == Exp_int(Str2Int(sx), 0) == 1;
      assert result_val == 1 % divisor;
    }
  } else {
    var half_n := n - 1;
    var half_sy := sy[0..|sy|-1];
    assert |half_sy| == n;
    var half_res := ModExpPow2(sx, half_sy, half_n, sz);
    
    var divisor := Str2Int(sz);
    var half_val := Str2Int(half_res);
    assert half_val == Exp_int(Str2Int(sx), Str2Int(half_sy)) % divisor;
    
    var mod_result := (half_val * half_val) % divisor;
    
    Str2IntLemma(sy);
    if sy[|sy|-1] == '1' {
      mod_result := (mod_result * (Str2Int(sx) % divisor)) % divisor;
      ExpIntPlusOne(Str2Int(sx), Str2Int(half_sy));
      assert Exp_int(Str2Int(sx), Str2Int(sy)) == Str2Int(sx) * Exp_int(Str2Int(sx), 2 * Str2Int(half_sy));
      assert Exp_int(Str2Int(sx), 2 * Str2Int(half_sy)) == Exp_int(Str2Int(sx), Str2Int(half_sy)) * Exp_int(Str2Int(sx), Str2Int(half_sy));
    } else {
      ExpIntSquared(Str2Int(sx), Str2Int(half_sy));
      assert Exp_int(Str2Int(sx), Str2Int(sy)) == Exp_int(Str2Int(sx), 2 * Str2Int(half_sy)) 
             == Exp_int(Str2Int(sx), Str2Int(half_sy)) * Exp_int(Str2Int(sx), Str2Int(half_sy));
    }
    
    res := IntToBitString(mod_result);
  }
}
// </vc-code>

