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
lemma AllZero_implies_Str2IntZero(s: string)
  requires ValidBitString(s)
  requires forall k | 0 <= k < |s| :: s[k] == '0'
  ensures Str2Int(s) == 0
  decreases |s|
{
  if |s| == 0 {
    assert Str2Int(s) == 0;
  } else {
    var prefix := s[0..|s|-1];
    assert Str2Int(s) == 2 * Str2Int(prefix) + (if s[|s|-1] == '1' then 1 else 0);
    assert s[|s|-1] == '0';
    assert Str2Int(s) == 2 * Str2Int(prefix) + 0;
    AllZero_implies_Str2IntZero(prefix);
    assert Str2Int(prefix) == 0;
    assert Str2Int(s) == 0;
  }
}

lemma ExistsOne_implies_Str2IntNonZero(s: string)
  requires ValidBitString(s)
  requires exists k | 0 <= k < |s| :: s[k] == '1'
  ensures Str2Int(s) > 0
  decreases |s|
{
  var k :| 0 <= k < |s| && s[k] == '1';
  if k == |s| - 1 {
    assert Str2Int(s) == 2 * Str2Int(s[0..|s|-1]) + 1;
    assert Str2Int(s) > 0;
  } else {
    var prefix := s[0..|s|-1];
    assert 0 <= k < |prefix| && prefix[k] == '1';
    ExistsOne_implies_Str2IntNonZero(prefix);
    assert Str2Int(prefix) > 0;
    assert Str2Int(s) == 2 * Str2Int(prefix) + (if s[|s|-1] == '1' then 1 else 0);
    assert Str2Int(s) >= 2 * Str2Int(prefix);
    assert Str2Int(s) > 0;
  }
}

lemma Exp_int_div2(n: nat)
  requires n > 0
  ensures Exp_int(2, n) == 2 * Exp_int(2, n-1)
  decreases n
{
  // By definition of Exp_int
  assert Exp_int(2, n) == 2 * Exp_int(2, n-1);
}

lemma PowerPrefixOfPowerOfTwo(s: string, n: nat)
  requires ValidBitString(s)
  requires Str2Int(s) == Exp_int(2, n)
  requires |s| == n + 1
  requires n > 0
  ensures Str2Int(s[0..|s|-1]) == Exp_int(2, n-1)
  ensures s[|s|-1] == '0'
  decreases n
{
  var prefix := s[0..|s|-1];
  var last := if s[|s|-1] == '1' then 1 else 0;
  assert Str2Int(s) == 2 * Str2Int(prefix) + last;
  // By definition of Exp_int
  assert Exp_int(2, n) == 2 * Exp_int(2, n-1);
  assert 2 * Str2Int(prefix) + last == 2 * Exp_int(2, n-1);
  if last == 1 {
    // Then 1 == 2*(Exp_int(2,n-1) - Str2Int(prefix)), impossible since RHS is even.
    // Produce contradiction:
    assert 1 == 2 * (Exp_int(2, n-1) - Str2Int(prefix));
    assert 2 * (Exp_int(2, n-1) - Str2Int(prefix)) % 2 == 0;
    assert 1 % 2 == 1;
    assert false;
  } else {
    assert last == 0;
    assert 2 * Str2Int(prefix) == 2 * Exp_int(2, n-1);
    // cancel factor 2
    assert Str2Int(prefix) == Exp_int(2, n-1);
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
  // Compute result using ghost evaluation of Str2Int and Exp_int, then convert to binary.
  ghost var a := Str2Int(sx);
  ghost var y := Str2Int(sy);
  ghost var m := Str2Int(sz);
  ghost var exp := Exp_int(a, y);
  var remNat := exp % m;
  var remStr := NatToBin(remNat);
  return remStr;
}
// </vc-code>

