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

method DivMod(dividend: string, divisor: string) returns (quotient: string, remainder: string)
  requires ValidBitString(dividend) && ValidBitString(divisor)
  requires Str2Int(divisor) > 0
  ensures ValidBitString(quotient) && ValidBitString(remainder)
  ensures Str2Int(quotient) == Str2Int(dividend) / Str2Int(divisor)
  ensures Str2Int(remainder) == Str2Int(dividend) % Str2Int(divisor)
{
  assume{:axiom} false;
}

// <vc-helpers>
function Nat2Str(x: nat, len: nat): string
  requires x < Exp_int(2, len)
  decreases len
{
  if len == 0 then "" else
    let prev := Nat2Str(x / 2, len - 1) in
    prev + (if x % 2 == 1 then "1" else "0")
}

lemma Nat2Str_ok(x: nat, len: nat)
  requires x < Exp_int(2, len)
  ensures ValidBitString(Nat2Str(x, len))
  ensures Str2Int(Nat2Str(x, len)) == x
  decreases len
{
  if len == 0 {
    // x < 1 implies x == 0, and Nat2Str(0,0) == ""
  } else {
    // let prev = Nat2Str(x/2, len-1)
    Nat2Str_ok(x / 2, len - 1);
    // show it yields the right integer
    // by definition Str2Int(prev + last) = 2*Str2Int(prev) + bit
    // and x = 2*(x/2) + x%2
  }
}

lemma Exp_add(a: nat, m: nat, n: nat)
  ensures Exp_int(a, m) * Exp_int(a, n) == Exp_int(a, m + n)
  decreases n
{
  if n == 0 {
    // Exp_int(a,0) == 1
  } else {
    Exp_add(a, m, n - 1);
    // Exp_int(a, n) == a * Exp_int(a, n-1), so multiply and rearrange
  }
}

lemma Exp2_double(i: nat)
  ensures Exp_int(2, i) + Exp_int(2, i) == Exp_int(2, i + 1)
  decreases i
{
  if i == 0 {
    // 1 + 1 == 2
  } else {
    // Exp_int(2, i+1) == 2 * Exp_int(2,i)
    // by unfolding Exp_int
    Exp2_double(i - 1);
    // the arithmetic follows from definitions
  }
}

lemma Bin2Nat_lt_pow(s: string)
  ensures Bin2Nat(s) < Exp_int(2, |s|)
  decreases s
{
  if |s| == 0 {
    // 0 < 1
  } else {
    var p := s[0..|s|-1];
    Bin2Nat_lt_pow(p);
    // Bin2Nat(s) = 2*Bin2Nat(p) + bit <= 2*(2^{|p|}-1) + 1 = 2^{|p|+1}-1 < 2^{|p|}
  }
}
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
  var z := Bin2Nat(sz);
  assert Bin2Nat(sz) == Str2Int(sz);
  if Bin2Nat(sy) == 0 {
    // 1 % z < 2^{|sz|}
    assert z > 1;
    assert Bin2Nat_lt_pow(sz);
    res := Nat2Str(1 % z, |sz|);
    return;
  }
  var v := Bin2Nat(sx) % z;
  assert Bin2Nat(sx) == Str2Int(sx);
  assert v == Str2Int(sx) % z;
  var i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant v < z
    invariant v == Exp_int(Str2Int(sx), Exp_int(2, i)) % z
  {
    var oldv := v;
    ghost var big := Exp_int(2, i);
    // use exponent addition lemma to relate products of powers
    Exp_add(Str2Int(sx), big, big);
    Exp2_double(i);
    v := (oldv * oldv) % z;
    assert oldv == Exp_int(Str2Int(sx), big) % z;
    assert v == (Exp_int(Str2Int(sx), big) * Exp_int(Str2Int(sx), big)) % z;
    assert Exp_int(Str2Int(sx), big) * Exp_int(Str2Int(sx), big) == Exp_int(Str2Int(sx), big + big);
    assert big + big == Exp_int(2, i + 1);
    assert v == Exp_int(Str2Int(sx), Exp_int(2, i + 1)) % z;
    i := i + 1;
  }
  // v < z and Bin2Nat(sz) < 2^{|sz|} imply v < 2^{|sz|}
  assert Bin2Nat_lt_pow(sz);
  assert v < Exp_int(2, |sz|);
  res := Nat2Str(v, |sz|);
}
// </vc-code>

