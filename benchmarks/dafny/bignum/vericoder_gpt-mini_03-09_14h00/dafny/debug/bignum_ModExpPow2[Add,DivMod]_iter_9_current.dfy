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
  if len == 0 then "" else Nat2Str(x / 2, len - 1) + (if x % 2 == 1 then "1" else "0")
}

function Bin2Nat(s: string): nat
  requires ValidBitString(s)
  decreases s
{
  // Alias to the existing Str2Int function to keep a single canonical definition
  Str2Int(s)
}

lemma Str2Int_concat(p: string, isOne: bool)
  requires ValidBitString(p)
  ensures Str2Int(p + (if isOne then "1" else "0")) == 2 * Str2Int(p) + (if isOne then 1 else 0)
  decreases p
{
  if |p| == 0 {
    // Str2Int("1") == 1, Str2Int("0") == 0
  } else {
    var q := p[0..|p|-1];
    Str2Int_concat(q, isOne);
  }
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
    // prove for prefix
    Nat2Str_ok(x / 2, len - 1);
    var prev := Nat2Str(x / 2, len - 1);
    assert ValidBitString(prev);
    var bitIsOne := x % 2 == 1;
    // apply concatenation lemma to get Str2Int(prev + last) = 2*Str2Int(prev) + bit
    Str2Int_concat(prev, bitIsOne);
    assert Str2Int(prev) == x / 2;
    // compute Str2Int of the full string
    assert Str2Int(Nat2Str(x, len)) == 2 * Str2Int(prev) + (if bitIsOne then 1 else 0);
    // arithmetic: 2*(x/2) + x%2 == x
    assert 2 * (x / 2) + (if bitIsOne then 1 else 0) == x;
  }
}

lemma Bin2Nat_lt_pow(s: string)
  requires ValidBitString(s)
  ensures Bin2Nat(s) < Exp_int(2, |s|)
  decreases s
{
  if |s| == 0 {
    // Str2Int("") == 0 < 1
  } else {
    var p := s[0..|s|-1];
    Bin2Nat_lt_pow(p);
    var bitIsOne := s[|s|-1] == '1';
    // relate Bin2Nat(s) to Bin2Nat(p)
    Str2Int_concat(p, bitIsOne);
    // Bin2Nat(s) == 2*Bin2Nat(p) + bit
    assert Bin2Nat(s) == 2 * Bin2Nat(p) + (if bitIsOne then 1 else 0);
    // Bin2Nat(p) < 2^{|p|}
    assert Bin2Nat(p) < Exp_int(2, |p|);
    // thus Bin2Nat(s) < 2 * Exp_int(2, |p|)
    assert Bin2Nat(s) < 2 * Exp_int(2, |p|);
    // 2 * 2^{|p|} == 2^{|p|+1}
    Exp2_double(|p|);
    assert 2 * Exp_int(2, |p|) == Exp_int(2, |p| + 1);
    assert Bin2Nat(s) < Exp_int(2, |p| + 1);
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

