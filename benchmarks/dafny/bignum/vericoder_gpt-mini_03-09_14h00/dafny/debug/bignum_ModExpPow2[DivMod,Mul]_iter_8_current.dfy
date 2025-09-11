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
lemma Exp_double(a: nat, b: nat)
  ensures Exp_int(a, 2*b) == Exp_int(a, b) * Exp_int(a, b)
  decreases b
{
  if b == 0 {
    assert Exp_int(a, 0) == 1;
    assert Exp_int(a, 0) * Exp_int(a, 0) == 1;
    assert Exp_int(a, 2*0) == Exp_int(a, 0) * Exp_int(a, 0);
  } else {
    // Inductive hypothesis
    Exp_double(a, b - 1);

    // Expand definitions
    assert Exp_int(a, 2*b) == a * Exp_int(a, 2*b - 1);
    assert Exp_int(a, 2*b - 1) == a * Exp_int(a, 2*b - 2);
    assert Exp_int(a, b) == a * Exp_int(a, b - 1);

    // Use IH: Exp_int(a, 2*(b-1)) == Exp_int(a, b-1) * Exp_int(a, b-1)
    assert Exp_int(a, 2*b - 2) == Exp_int(a, b - 1) * Exp_int(a, b - 1);

    // Combine
    assert Exp_int(a, 2*b) == a * (a * Exp_int(a, 2*b - 2));
    assert Exp_int(a, 2*b) == a * a * (Exp_int(a, b - 1) * Exp_int(a, b - 1));
    assert Exp_int(a, 2*b) == (a * Exp_int(a, b - 1)) * (a * Exp_int(a, b - 1));
    assert Exp_int(a, 2*b) == Exp_int(a, b) * Exp_int(a, b);
  }
}

lemma ModSquareExp(a: nat, b: nat, m: nat)
  requires m > 0
  ensures (Exp_int(a, b) % m) * (Exp_int(a, b) % m) % m == Exp_int(a, 2*b) % m
  decreases b
{
  var x := Exp_int(a, b);
  var q := x / m;
  var r := x % m;
  assert x == q * m + r;

  // Square both sides
  assert x * x == (q * m + r) * (q * m + r);
  assert x * x == q * m * q * m + 2 * q * m * r + r * r;
  // Show the first two terms are multiples of m
  var t := q * m * q + 2 * q * r;
  assert q * m * q * m + 2 * q * m * r == m * t;
  // Therefore (x*x) % m == (r*r) % m
  assert (x * x) % m == (m * t + r * r) % m;
  assert (m * t) % m == 0;
  assert (x * x) % m == r * r % m;

  // Use Exp_double to relate x*x to Exp_int(a,2*b)
  Exp_double(a, b);
  assert Exp_int(a, 2*b) == x * x;
  assert Exp_int(a, 2*b) % m == (x * x) % m;
  assert Exp_int(a, 2*b) % m == r * r % m;
  assert r * r % m == (x % m) * (x % m) % m;
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
  ghost {
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
    Exp_int_div2(n);
    assert Exp_int(2, n) == 2 * Exp_int(2, n-1);
    assert Str2Int(sy) == 2 * Str2Int(sy1);

    assert prodNat % m == Exp_int(a, Str2Int(sy)) % m;
    assert remNat == Exp_int(a, Str2Int(sy)) % m;
  }
  var remStr := NatToBin(remNat);
  return remStr;
}
// </vc-code>

