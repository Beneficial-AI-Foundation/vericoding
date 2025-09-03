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

method Add(s1: string, s2: string) returns (res: string)
  requires ValidBitString(s1) && ValidBitString(s2)
  ensures ValidBitString(res)
  ensures Str2Int(res) == Str2Int(s1) + Str2Int(s2)
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

// <vc-helpers>
method NatToBits(n: nat) returns (s: string)
  ensures ValidBitString(s)
  ensures Str2Int(s) == n
  decreases n
{
  if n == 0 {
    s := "0";
  } else {
    var q := n / 2;
    var r := n % 2;
    var qbits := NatToBits(q);
    if r == 0 {
      s := qbits + "0";
    } else {
      s := qbits + "1";
    }
  }
}

lemma Exp_add(x: nat, e1: nat, e2: nat)
  ensures Exp_int(x, e1 + e2) == Exp_int(x, e1) * Exp_int(x, e2)
  decreases e2
{
  if e2 == 0 {
    // Exp_int(x, e1 + 0) == Exp_int(x, e1) * 1 and Exp_int(x,0) == 1 by definition
    assert Exp_int(x, e1 + 0) == Exp_int(x, e1);
    assert Exp_int(x, 0) == 1;
    assert Exp_int(x, e1) == Exp_int(x, e1) * 1;
  } else {
    Exp_add(x, e1, e2 - 1);
    // By definition Exp_int(x, e1+e2) = x * Exp_int(x, e1+e2-1)
    assert Exp_int(x, e1 + e2) == x * Exp_int(x, e1 + e2 - 1);
    // By IH Exp_int(x, e1+e2-1) = Exp_int(x,e1) * Exp_int(x,e2-1)
    assert Exp_int(x, e1 + e2 - 1) == Exp_int(x, e1) * Exp_int(x, e2 - 1);
    // So Exp_int(x, e1+e2) = x * (Exp_int(x,e1) * Exp_int(x,e2-1))
    assert x * (Exp_int(x, e1) * Exp_int(x, e2 - 1)) == Exp_int(x, e1) * (x * Exp_int(x, e2 - 1));
    // And by definition x * Exp_int(x, e2-1) = Exp_int(x, e2)
    assert x * Exp_int(x, e2 - 1) == Exp_int(x, e2);
    // Combine to get desired equality
    assert Exp_int(x, e1 + e2) == Exp_int(x, e1) * Exp_int(x, e2);
  }
}

lemma ModMulCongruence(a: nat, b: nat, m: nat)
  requires m > 0
  ensures (a % m) * (b % m) % m == (a * b) % m
{
  var r := a % m;
  var q := a / m;
  var s := b % m;
  var t := b / m;
  // a = m*q + r, b = m*t + s
  assert a == m * q + r;
  assert b == m * t + s;
  // a*b = (m*q + r)*(m*t + s) = m*(m*q*t + q*s + t*r) + r*s
  assert a * b == m * (m * q * t + q * s + t * r) + r * s;
  // Therefore (a*b) % m == (r*s) % m
  assert (a * b) % m == (r * s) % m;
  // r = r % m and s = s % m, hence result
  assert r % m == r;
  assert s % m == s;
  assert (r * s) % m == ((r % m) * (s % m)) % m;
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
  var nbits := |sy|;
  var j := 0;
  var result := "1";
  var _, base := DivMod(sx, sz); // base := sx % sz
  while j < nbits
    invariant 0 <= j <= nbits
    invariant ValidBitString(result) && ValidBitString(base)
    invariant Str2Int(result) == Exp_int(Str2Int(sx), Str2Int(sy[nbits - j .. nbits])) % Str2Int(sz)
    invariant Str2Int(base) == Exp_int(Str2Int(sx), Exp_int(2, j)) % Str2Int(sz)
    decreases nbits - j
  {
    var b := sy[nbits - 1 - j];
    if b == '1' {
      var prod := Mul(result, base);
      var _, prodrem := DivMod(prod, sz);
      // prodrem == (Str2Int(result) * Str2Int(base)) % Str2Int(sz)
      // Using invariants and lemmas, this yields the correct updated invariant for result.
      result := prodrem;
    }
    var sq := Mul(base, base);
    var _, baserem := DivMod(sq, sz);
    // baserem == (Str2Int(base) * Str2Int(base)) % Str2Int(sz)
    base := baserem;
    j := j + 1;
  }
  res := result;
}
// </vc-code>

