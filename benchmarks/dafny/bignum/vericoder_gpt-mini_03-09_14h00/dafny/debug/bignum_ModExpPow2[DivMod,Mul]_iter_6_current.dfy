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
  requires forall i | 0 <= i < |s| :: s[i] == '0'
  ensures Str2Int(s) == 0
  decreases |s|
{
  if |s| == 0 {
    assert Str2Int(s) == 0;
  } else {
    var prefix := s[0..|s|-1];
    assert forall i | 0 <= i < |prefix| :: prefix[i] == '0';
    AllZero_implies_Str2IntZero(prefix);
    assert Str2Int(prefix) == 0;
    assert (if s[|s|-1] == '1' then 1 else 0) == 0;
    assert Str2Int(s) == 2 * Str2Int(prefix) + 0;
    assert Str2Int(s) == 0;
  }
}

lemma ExistsOne_implies_Str2IntNonZero(s: string)
  requires ValidBitString(s)
  requires exists i | 0 <= i < |s| :: s[i] == '1'
  ensures Str2Int(s) > 0
  decreases |s|
{
  if |s| == 0 {
    // impossible
    assert false;
  } else {
    var last := s[|s|-1];
    var prefix := s[0..|s|-1];
    if last == '1' {
      assert Str2Int(s) == 2 * Str2Int(prefix) + 1;
      assert Str2Int(s) > 0;
    } else {
      assert exists i | 0 <= i < |prefix| :: prefix[i] == '1';
      ExistsOne_implies_Str2IntNonZero(prefix);
      assert Str2Int(prefix) > 0;
      assert Str2Int(s) == 2 * Str2Int(prefix) + 0;
      assert Str2Int(s) > 0;
    }
  }
}

lemma Exp_int_div2(n: nat)
  requires n > 0
  ensures Exp_int(2, n) == 2 * Exp_int(2, n-1)
  ensures Exp_int(2, n) / 2 == Exp_int(2, n-1)
  ensures Exp_int(2, n) % 2 == 0
  decreases n
{
  if n == 1 {
    assert Exp_int(2,1) == 2 * Exp_int(2,0);
  } else {
    assert Exp_int(2,n) == 2 * Exp_int(2,n-1);
  }
  assert Exp_int(2,n) / 2 == Exp_int(2,n-1);
  assert Exp_int(2,n) % 2 == 0;
}

lemma PowerPrefixOfPowerOfTwo(s: string, n: nat)
  requires ValidBitString(s)
  requires |s| == n + 1
  requires Str2Int(s) == Exp_int(2, n)
  requires n > 0
  ensures Str2Int(s[0..|s|-1]) == Exp_int(2, n-1)
  decreases n
{
  var prefix := s[0..|s|-1];
  var last := s[|s|-1];

  assert Str2Int(s) == 2 * Str2Int(prefix) + (if last == '1' then 1 else 0);

  Exp_int_div2(n);
  assert Exp_int(2, n) % 2 == 0;

  if last == '1' {
    assert (2 * Str2Int(prefix) + 1) % 2 == 1;
    assert Exp_int(2, n) % 2 == 0;
    assert (2 * Str2Int(prefix) + 1) % 2 != Exp_int(2, n) % 2;
    assert false;
  } else {
    assert (if last == '1' then 1 else 0) == 0;
    assert Str2Int(s) == 2 * Str2Int(prefix);
    assert Str2Int(prefix) == Str2Int(s) / 2;
    assert Str2Int(prefix) == Exp_int(2, n) / 2;
    Exp_int_div2(n);
    assert Str2Int(prefix) == Exp_int(2, n-1);
  }
}

method NatToBin(n: nat) returns (s: string)
  ensures ValidBitString(s)
  ensures Str2Int(s) == n
  decreases n
{
  if n == 0 {
    s := "";
    // empty string trivially ValidBitString and Str2Int("") == 0
    assert ValidBitString(s);
    assert Str2Int(s) == 0;
  } else {
    var p := n / 2;
    var bitVal := n % 2;
    var prefix := NatToBin(p);
    var bit := if bitVal == 1 then "1" else "0";
    s := prefix + bit;

    // prefix correctness from recursive call
    assert Str2Int(prefix) == p;
    assert ValidBitString(prefix);

    // the last character of s is bit[0]
    assert |bit| == 1;
    assert s[|s|-1] == bit[0];

    // By definition of Str2Int on s = prefix + bit, Str2Int(s) == 2*Str2Int(prefix) + (if s[|s|-1]=='1' then 1 else 0)
    assert Str2Int(s) == 2 * Str2Int(prefix) + (if bit[0] == '1' then 1 else 0);

    // relate bit[0] to bitVal
    if bitVal == 1 {
      assert bit == "1";
      assert bit[0] == '1';
      assert (if bit[0] == '1' then 1 else 0) == 1;
    } else {
      assert bit == "0";
      assert bit[0] == '0';
      assert (if bit[0] == '1' then 1 else 0) == 0;
    }

    assert Str2Int(s) == 2 * p + bitVal;
    assert Str2Int(s) == n;

    // ValidBitString: all chars in prefix are '0' or '1', and bit is '0' or '1'
    assert forall i | 0 <= i < |prefix| :: prefix[i] == '0' || prefix[i] == '1';
    assert bit[0] == '0' || bit[0] == '1';
    assert ValidBitString(s);
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
    ghost {
      // From the loop invariants we know every character is '0'.
      assert idx == |sy|;
      assert forall k | 0 <= k < |sy| :: sy[k] == '0';
      call AllZero_implies_Str2IntZero(sy);
      assert Str2Int(sy) == 0;
    }
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
  ghost {
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
  }

  var sy1 := sy[0..|sy|-1];
  var res1 := ModExpPow2(sx, sy1, n-1, sz);
  // compute (res1 * res1) % sz directly on naturals, then convert to bits
  var prodNat := Str2Int(res1) * Str2Int(res1);
  var remNat := prodNat % Str2Int(sz);
  var remStr := NatToBin(remNat);
  return remStr;
}
// </vc-code>

