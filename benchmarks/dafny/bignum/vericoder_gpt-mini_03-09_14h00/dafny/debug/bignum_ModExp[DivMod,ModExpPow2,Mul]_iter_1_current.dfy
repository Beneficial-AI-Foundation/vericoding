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

method Mul(s1: string, s2: string) returns (res: string)
  requires ValidBitString(s1) && ValidBitString(s2)
  ensures ValidBitString(res)
  ensures Str2Int(res) == Str2Int(s1) * Str2Int(s2)
{
  assume{:axiom} false;
}

// <vc-helpers>
method ParseBitString(s: string) returns (n: nat)
  requires ValidBitString(s)
  ensures n == Str2Int(s)
  decreases s
{
  var acc := 0;
  var i := 0;
  while i < |s|
    invariant 0 <= i <= |s|
    invariant acc == Str2Int(s[0..i])
    decreases |s| - i
  {
    var c := s[i];
    if c == '1' {
      acc := acc * 2 + 1;
    } else {
      acc := acc * 2 + 0;
    }
    i := i + 1;
  }
  n := acc;
}

method NatToBits(n: nat) returns (s: string)
  ensures ValidBitString(s)
  ensures Str2Int(s) == n
  decreases n
{
  if n == 0 {
    s := "0";
    return;
  }
  var prefix := NatToBits(n / 2);
  var last := if n % 2 == 1 then "1" else "0";
  s := prefix + last;
}

lemma MulMod(x: nat, y: nat, m: nat)
  requires m > 0
  ensures (x % m) * y % m == (x * y) % m
{
  var q := x / m;
  var r := x % m;
  assert x == q * m + r;
  // (q*m + r) * y = q*m*y + r*y, so modulo m the q*m*y part vanishes.
  assert (x * y) % m == (r * y) % m;
  assert (r * y) % m == ( (x % m) * y ) % m;
}

method PowMod(a: nat, e: nat, m: nat) returns (r: nat)
  requires m > 0
  ensures r == Exp_int(a, e) % m
  decreases e
{
  var res := 1 % m;
  var exp := e;
  while exp > 0
    invariant 0 <= exp <= e
    invariant res * Exp_int(a, exp) % m == Exp_int(a, e) % m
    decreases exp
  {
    // res' = (res * a) % m; exp' = exp - 1
    var tmp := (res * a) % m;
    // Use MulMod lemma to reason about modular arithmetic:
    // ((res*a) % m) * Exp_int(a, exp-1) % m == (res*a*Exp_int(a, exp-1)) % m
    // and a * Exp_int(a, exp-1) == Exp_int(a, exp)
    res := tmp;
    exp := exp - 1;
  }
  r := res;
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
  var a := ParseBitString(sx);
  var e := ParseBitString(sy);
  var m := ParseBitString(sz);
  var rnat := PowMod(a, e, m);
  var sres := NatToBits(rnat);
  // Connect string result with required ensures:
  res := sres;
}
// </vc-code>

