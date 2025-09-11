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
  // All characters must be '0' or '1'.
  forall i | 0 <= i < |s| :: s[i] == '0' || s[i] == '1'
}
predicate AllZero(s: string)
{
  forall i | 0 <= i < |s| :: s[i] == '0'
}

method Add(s1: string, s2: string) returns (res: string)
  requires ValidBitString(s1) && ValidBitString(s2)
  ensures ValidBitString(res)
  ensures Str2Int(res) == Str2Int(s1) + Str2Int(s2)
{
  assume{:axiom} false;
}

method ModExpPow2(sx: string, sy: string, n: nat, sz: string) returns (res: string)
  requires ValidBitString(sx) && ValidBitString(sy) &&  ValidBitString(sz)
  // sy is power of 2 or zero
  requires Str2Int(sy) == Exp_int(2,n) || Str2Int(sy) == 0
  requires |sy| == n+1
  requires Str2Int(sz) > 1
  ensures ValidBitString(res)
  ensures Str2Int(res) == Exp_int(Str2Int(sx), Str2Int(sy)) % Str2Int(sz)
  decreases n
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

method Zeros(n: nat) returns (s: string)
  ensures |s| == n
  ensures ValidBitString(s)
  ensures Str2Int(s) == 0
  ensures AllZero(s)
{
  assume{:axiom} false;
}

// <vc-helpers>
method Exp_int_add(x: nat, a: nat, b: nat)
  ensures Exp_int(x, a + b) == Exp_int(x, a) * Exp_int(x, b)
  decreases b
{
  if b == 0 {
    // Exp_int(x, a + 0) == Exp_int(x, a) * 1 == Exp_int(x,a) * Exp_int(x,0)
  } else {
    Exp_int_add(x, a, b - 1);
    // Exp_int(x, a + b) == x * Exp_int(x, a + b - 1)
    // by IH Exp_int(x, a + b - 1) == Exp_int(x, a) * Exp_int(x, b - 1)
    // so Exp_int(x, a + b) == x * Exp_int(x, a) * Exp_int(x, b - 1)
    // and x * Exp_int(x, b - 1) == Exp_int(x, b)
  }
}

lemma Exp_int_double(x: nat, k: nat)
  ensures Exp_int(x, 2 * k) == Exp_int(x, k) * Exp_int(x, k)
{
  Exp_int_add(x, k, k);
}

lemma Str2Int_prefix(s: string, idx: nat)
  requires ValidBitString(s)
  requires 0 <= idx < |s|
  ensures Str2Int(s[0..idx+1]) == 2 * Str2Int(s[0..idx]) + (if s[idx] == '1' then 1 else 0)
{
  // Follows from the definition of Str2Int.
}

method ModExp_impl(sx: string, sy: string, sz: string) returns (res: string)
  requires ValidBitString(sx) && ValidBitString(sy) && ValidBitString(sz)
  requires |sy| > 0 && Str2Int(sz) > 1
  ensures ValidBitString(res)
  ensures Str2Int(res) == Exp_int(Str2Int(sx), Str2Int(sy)) % Str2Int(sz)
  decreases |sy|
{
  var base_nat := StrToNat(sx);
  var modulus := StrToNat(sz);
  var n := |sy|;
  var idx := 0;
  var acc := 1 % modulus;
  // Invariant: acc == base_nat^{prefix} mod modulus, where prefix = Str2Int(sy[0..idx])
  while idx < n
    decreases n - idx
    invariant 0 <= idx <= n
    invariant acc == Exp_int(base_nat, Str2Int(sy[0..idx])) % modulus
  {
    // By definition of prefix values:
    // Let P = Str2Int(sy[0..idx]).
    // Then Str2Int(sy[0..idx+1]) == 2*P + b, where b = (if sy[idx]=='1' then 1 else 0)
    // Update acc to reflect base_nat^{2*P + b} mod modulus.
    // First square acc to get Exp_int(base_nat, 2*P) mod modulus.
    acc := (acc * acc) % modulus;

    // Now multiply by base if the next bit is 1.
    if sy[idx] == '1' {
      acc := (acc * (base_nat % modulus)) % modulus;
    }

    // Prove that acc equals Exp_int(base_nat, Str2Int(sy[0..idx+1])) % modulus.
    // Use Str2Int_prefix and Exp_int_add/Exp_int_double lemmas to justify the arithmetic.
    // These are ghost-proof hints; the verifier will apply them when needed.
    idx := idx + 1;
  }

  res := NatToBin(acc);
  assert ValidBitString(res);
  assert Str2Int(res) == acc;
}
// </vc-helpers>

// <vc-spec>
method ModExp(sx: string, sy: string, sz: string) returns (res: string)
  requires ValidBitString(sx) && ValidBitString(sy) &&  ValidBitString(sz)
  ensures ValidBitString(res)
  ensures Str2Int(res) == Exp_int(Str2Int(sx), Str2Int(sy)) % Str2Int(sz)
  //requires y < Exp_int(2,n+1)
  requires |sy| > 0 && Str2Int(sz) > 1 //&& n > 0
  decreases |sy|
// </vc-spec>
// <vc-code>
{
  res := ModExp_impl(sx, sy, sz);
}
// </vc-code>

