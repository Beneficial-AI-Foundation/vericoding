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

method DivMod(dividend: string, divisor: string) returns (quotient: string, remainder: string)
  requires ValidBitString(dividend) && ValidBitString(divisor)
  requires Str2Int(divisor) > 0
  ensures ValidBitString(quotient) && ValidBitString(remainder)
  ensures Str2Int(quotient) == Str2Int(dividend) / Str2Int(divisor)
  ensures Str2Int(remainder) == Str2Int(dividend) % Str2Int(divisor)
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

method Zeros(n: nat) returns (s: string)
  ensures |s| == n
  ensures ValidBitString(s)
  ensures Str2Int(s) == 0
  ensures AllZero(s)
{
  assume{:axiom} false;
}

// <vc-helpers>
function Str2Int(s: string): nat
  requires ValidBitString(s)
  decreases s
{
  if |s| == 0 then  0  else  (2 * Str2Int(s[0..|s|-1]) + (if s[|s|-1] == '1' then 1 else 0))
}
function Exp_int(x: nat, y:nat): nat
{
  if y == 0 then 1 else x * Exp_int(x, y - 1)
}
function Nat2Str(x: nat): string
  ensures ValidBitString(Nat2Str(x))
  ensures Str2Int(Nat2Str(x)) == x
  decreases x
{
  if x == 0 then "" else
    var q := x / 2;
    var r := x % 2;
    Nat2Str(q) + (if r == 1 then "1" else "0")
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
  var base := Str2Int(sx);
  var modulo := Str2Int(sz);
  var r: nat := 1;
  var i := 0;
  // Process bits from most-significant (index 0) to least-significant (index |sy|-1)
  while i < |sy|
    invariant 0 <= i <= |sy|
    invariant r == Exp_int(base, Str2Int(sy[0..i])) % modulo
  {
    var p := Str2Int(sy[0..i]);
    // square r: r := (r * r) % modulo;
    var rr := (r * r) % modulo;
    // r == Exp_int(base,p) % modulo, so square corresponds to Exp_int(base, 2*p) % modulo
    assert rr == (Exp_int(base, p) % modulo * Exp_int(base, p) % modulo) % modulo;
    MulMod(Exp_int(base, p), Exp_int(base, p), modulo);
    assert (Exp_int(base, p) % modulo * Exp_int(base, p) % modulo) % modulo == (Exp_int(base, p) * Exp_int(base, p)) % modulo;
    Exp_int_add_mul(base, p, p);
    assert (Exp_int(base, p) * Exp_int(base, p)) % modulo == Exp_int(base, 2 * p) % modulo;
    r := rr;
    if sy[i] == '1' {
      var rr2 := (r * base) % modulo;
      // r == Exp_int(base, 2*p) % modulo, so multiplying by base yields Exp_int(base, 2*p+1) % modulo
      assert rr2 == (Exp_int(base, 2 * p) % modulo * base % modulo) % modulo;
      MulMod(Exp_int(base, 2 * p), base, modulo);
      assert (Exp_int(base, 2 * p) % modulo * base % modulo) % modulo == (Exp_int(base, 2 * p) * base) % modulo;
      assert Exp_int(base, 2 * p + 1) == base * Exp_int(base, 2 * p);
      assert (Exp_int(base, 2 * p) * base) % modulo == Exp_int(base, 2 * p + 1) % modulo;
      r := rr2;
    }
    i := i + 1;
  }
  res := Nat2Str(r);
}
// </vc-code>

