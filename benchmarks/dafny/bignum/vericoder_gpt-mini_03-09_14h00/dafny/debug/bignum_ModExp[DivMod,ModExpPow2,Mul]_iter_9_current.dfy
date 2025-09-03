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
method NatToBits(n: nat) returns (s: string)
  ensures ValidBitString(s)
  ensures Str2Int(s) == n
  decreases n
{
  if n == 0 {
    s := "";
    return;
  }
  var q := n / 2;
  var r := n % 2;
  var prefix := NatToBits(q);
  var bit := if r == 1 then "1" else "0";
  s := prefix + bit;
  // Proof obligations
  assert ValidBitString(prefix);
  assert ValidBitString(bit);
  assert ValidBitString(s);
  reveal Str2Int;
  // Use lemma for the last-character relation
  Str2IntAppend(s, |s|-1);
  // For s = prefix + bit, the prefix is the slice excluding the last character, and last character equals bit[0].
  assert s[0..|s|-1] == prefix;
  assert s[|s|-1] == bit[0];
  // bit[0] corresponds to r
  if r == 1 {
    assert bit[0] == '1';
  } else {
    assert bit[0] == '0';
  }
  assert (if s[|s|-1] == '1' then 1 else 0) == r;
  // By recursive postcondition
  assert Str2Int(prefix) == q;
  assert Str2Int(s) == 2 * q + r;
  assert Str2Int(s) == n;
}

method ParseBitString(s: string) returns (n: nat)
  requires ValidBitString(s)
  ensures n == Str2Int(s)
  decreases s
{
  reveal Str2Int;
  var acc := 0;
  var i := 0;
  while i < |s|
    invariant 0 <= i <= |s|
    invariant acc == Str2Int(s[0..i])
    decreases |s| - i
  {
    var bit := if s[i] == '1' then 1 else 0;
    acc := acc * 2 + bit;
    // Use lemma to relate slices
    Str2IntAppend(s, i);
    // From invariant and lemma we get the new value
    assert acc == Str2Int(s[0..i+1]);
    i := i + 1;
  }
  n := acc;
}

lemma Str2IntAppend(s: string, i: nat)
  requires ValidBitString(s)
  requires 0 <= i < |s|
  ensures Str2Int(s[0..i+1]) == 2 * Str2Int(s[0..i]) + (if s[i] == '1' then 1 else 0)
{
  reveal Str2Int;
  assert Str2Int(s[0..i+1]) == 2 * Str2Int(s[0..i]) + (if s[i] == '1' then 1 else 0);
}

lemma MulMod(x: nat, y: nat, m: nat)
  requires m > 0
  ensures (x % m) * y % m == (x * y) % m
{
  var r := x % m;
  var k := x / m;
  // x = k*m + r
  assert x == k * m + r;
  // multiply both sides by y
  assert x * y == k * m * y + r * y;
  // (k*m*y) is divisible by m, so modulo m the product equals r*y mod m
  assert k * m * y == (k * y) * m;
  assert (k * y) * m % m == 0;
  assert (x * y) % m == (r * y) % m;
  // r == x % m, so the RHS is ((x % m) * y) % m
  assert (r * y) % m == ((x % m) * y) % m;
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
  res := sres;
}
// </vc-code>

