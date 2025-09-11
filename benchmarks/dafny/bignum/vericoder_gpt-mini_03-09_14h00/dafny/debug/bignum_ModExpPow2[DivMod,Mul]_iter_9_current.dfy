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
  call Exp_int_div2(n);
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
  // Scan sy to determine whether it is all zeros, while recording a witness index if a '1' is found.
  var idx := 0;
  var allZero := true;
  var found := false;
  var firstOneIndex := 0;
  while idx < |sy|
    invariant 0 <= idx <= |sy|
    invariant forall k | 0 <= k < idx :: sy[k] == '0'
    invariant found ==> 0 <= firstOneIndex < |sy|
    invariant found ==> sy[firstOneIndex] == '1'
  {
    if sy[idx] == '1' {
      allZero := false;
      found := true;
      firstOneIndex := idx;
      idx := |sy|;
    } else {
      idx := idx + 1;
    }
  }

  if allZero {
      // From the loop invariants we know every character is '0'.
      assert idx == |sy|;
      assert forall k | 0 <= k < |sy| :: sy[k] == '0';
      call AllZero_implies_Str2IntZero(sy);
      assert Str2Int(sy) == 0;
    // x^0 % sz == 1 % sz == 1 since Str2Int(sz) > 1
    return "1";
  }

  if n == 0 {
    // sy must be 1 when not zero and n == 0, so x^1 % sz == x % sz
    var remNat := Str2Int(sx) % Str2Int(sz);
    var remStr := NatToBin(remNat);
    return remStr;
  }

  // n > 0 and sy is not zero, so there exists a '1' in sy -> Str2Int(sy) > 0.
    assert found;
    assert 0 <= firstOneIndex < |sy|;
    assert sy[firstOneIndex] == '1';
    assert exists k | 0 <= k < |sy| :: sy[k] == '1';
    call ExistsOne_implies_Str2IntNonZero(sy);
    assert Str2Int(sy) > 0;
    // From the precondition (Str2Int(sy) == Exp_int(2,n) || Str2Int(sy) == 0) and Str2Int(sy) > 0,
    // we get Str2Int(sy) == Exp_int(2,n).
    if Str2Int(sy) == 0 {
      assert false;
    }
    assert Str2Int(sy) == Exp_int(2, n);
    call PowerPrefixOfPowerOfTwo(sy, n);

  var sy1 := sy[0..|sy|-1];
  var res1 := ModExpPow2(sx, sy1, n-1, sz);
  // compute (res1 * res1) % sz directly on naturals, then convert to bits
  var prodNat := Str2Int(res1) * Str2Int(res1);
  var remNat := prodNat % Str2Int(sz);
    var a := Str2Int(sx);
    var b := Str2Int(sy1);
    var m := Str2Int(sz);

    // From recursive call
    assert Str2Int(res1) == Exp_int(a, b) % m;

    // Use modular square lemma to relate prodNat % m to Exp_int(a, 2*b) % m
    call ModSquareExp(a, b, m);
    assert prodNat % m == Exp_int(a, 2*b) % m;

    // Relate 2*b to Str2Int(sy)
    // From earlier ghost reasoning we have Str2Int(sy) == Exp_int(2, n) and PowerPrefixOfPowerOfTwo gave Str2Int(sy1) == Exp_int(2, n-1)
    assert Str2Int(sy) == Exp_int(2, n);
    assert Str2Int(sy1) == Exp_int(2, n-1);
    call Exp_int_div2(n);
    assert Exp_int(2, n) == 2 * Exp_int(2, n-1);
    assert Str2Int(sy) == 2 * Str2Int(sy1);

    assert prodNat % m == Exp_int(a, Str2Int(sy)) % m;
    assert remNat == Exp_int(a, Str2Int(sy)) % m;
  var remStr := NatToBin(remNat);
  return remStr;
}
// </vc-code>

