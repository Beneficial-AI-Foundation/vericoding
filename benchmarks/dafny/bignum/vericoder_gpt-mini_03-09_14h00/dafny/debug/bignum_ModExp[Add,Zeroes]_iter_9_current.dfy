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

method Zeros(n: nat) returns (s: string)
  ensures |s| == n
  ensures ValidBitString(s)
  ensures Str2Int(s) == 0
  ensures AllZero(s)
{
  assume{:axiom} false;
}

// <vc-helpers>
lemma MulMod(a: nat, b: nat, m: nat)
  requires m > 0
  ensures (a * b) % m == ((a % m) * b) % m
{
  var q := a / m;
  var r := a % m;
  assert a == q * m + r;
  assert 0 <= r < m;
  assert a * b == q * m * b + r * b;
  assert (a * b) % m == (r * b) % m;
  assert ((a % m) * b) % m == (r * b) % m;
}

lemma PowDouble(a: nat, k: nat)
  ensures Exp_int(a * a, k) == Exp_int(a, 2 * k)
  decreases k
{
  if k == 0 {
  } else {
    PowDouble(a, k - 1);
    // Exp_int(a*a, k) = (a*a) * Exp_int(a*a, k-1)
    // Exp_int(a, 2*k) = a * Exp_int(a, 2*k-1) = a * a * Exp_int(a, 2*k-2) = (a*a) * Exp_int(a, 2*(k-1))
    assert Exp_int(a * a, k) == (a * a) * Exp_int(a * a, k - 1);
    assert Exp_int(a, 2 * k) == (a * a) * Exp_int(a, 2 * (k - 1));
    assert Exp_int(a * a, k - 1) == Exp_int(a, 2 * (k - 1));
  }
}

lemma ModPow(a: nat, e: nat, m: nat)
  requires m > 0
  ensures Exp_int(a % m, e) % m == Exp_int(a, e) % m
  decreases e
{
  if e == 0 {
    // both sides are 1 % m
  } else {
    ModPow(a, e - 1, m);
    // Exp_int(a% m, e) = (a % m) * Exp_int(a % m, e-1)
    // Exp_int(a, e) = a * Exp_int(a, e-1)
    // By MulMod: (a * Exp_int(a, e-1)) % m == ((a % m) * Exp_int(a, e-1)) % m
    MulMod(a, Exp_int(a, e - 1), m);
    // From the induction hypothesis: Exp_int(a % m, e-1) % m == Exp_int(a, e-1) % m
    // So ((a % m) * Exp_int(a % m, e-1)) % m == ((a % m) * Exp_int(a, e-1)) % m
    MulMod(Exp_int(a % m, e - 1), (a % m), m);
    // Combining the equalities above yields the required result.
  }
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
  var m := ParseBits(sz);
  var origB := ParseBits(sx);
  var origE := ParseBits(sy);

  assert m > 1;

  var resNat := 1 % m;
  var a := origB % m;
  var e := origE;

  while e > 0
    decreases e
    invariant 0 <= e
    invariant 0 <= resNat < m
    invariant 0 <= a < m
    invariant resNat * Exp_int(a, e) % m == Exp_int(origB, origE) % m
  {
    if e % 2 == 1 {
      var oldRes := resNat;
      var oldE := e;
      // update result by multiplying by a (mod m)
      resNat := resNat * a % m;
      e := e - 1;
      // show invariant holds after this update
      // (oldRes * a % m) * Exp_int(a, oldE-1) % m == (oldRes * a * Exp_int(a, oldE-1)) % m
      MulMod(oldRes * a, Exp_int(a, oldE - 1), m);
      // and (oldRes * a * Exp_int(a, oldE-1)) % m == oldRes * Exp_int(a, oldE) % m by definition
      assert resNat * Exp_int(a, e) % m == oldRes * Exp_int(a, oldE) % m;
    }
    if e > 0 {
      var oldA := a;
      var oldE := e;
      a := a * a % m;
      e := e / 2;
      // show invariant holds after squaring base and halving exponent
      // Use PowDouble to rewrite Exp_int(oldA, oldE) as Exp_int(oldA*oldA, oldE/2)
      PowDouble(oldA, oldE / 2);
      // Use ModPow to relate Exp_int((oldA*oldA) % m, oldE/2) % m to Exp_int(oldA*oldA, oldE/2) % m
      ModPow(oldA * oldA, oldE / 2, m);
      // Now combine to conclude:
      // resNat * Exp_int(a, e) % m == resNat * Exp_int(oldA*oldA, oldE/2) % m == resNat * Exp_int(oldA, oldE) % m
      // This preserves the invariant.
      assert resNat * Exp_int(a, e) % m == resNat * Exp_int(oldA, oldE) % m;
    }
  }

  res := BuildBinary(|sz|, resNat);
}
// </vc-code>

