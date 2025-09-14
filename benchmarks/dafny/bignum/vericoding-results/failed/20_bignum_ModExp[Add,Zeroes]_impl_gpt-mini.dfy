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
function ParseBits(s: string): nat
  requires ValidBitString(s)
{
  Str2Int(s)
}

function BuildBinary(len: nat, v: nat): string
  requires v < Exp_int(2, len)
  ensures ValidBitString(result)
  ensures |result| == len
  ensures Str2Int(result) == v
  decreases len
{
  if len == 0 then "" else BuildBinary(len - 1, v / 2) + (if v % 2 == 1 then "1" else "0")
}

lemma BitStringBound(s: string)
  ensures Str2Int(s) < Exp_int(2, |s|)
  decreases s
{
  if |s| == 0 {
  } else {
    BitStringBound(s[0..|s|-1]);
    var prefix := s[0..|s|-1];
    var bit := if s[|s|-1] == '1' then 1 else 0;
    assert Str2Int(s) == 2 * Str2Int(prefix) + bit;
    assert Str2Int(prefix) < Exp_int(2, |prefix|);
    assert 2 * Str2Int(prefix) < 2 * Exp_int(2, |prefix|);
    assert 2 * Exp_int(2, |prefix|) == Exp_int(2, |prefix| + 1);
    assert |prefix| + 1 == |s|;
    assert Str2Int(s) < Exp_int(2, |s|);
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

  // Relate reduced-base exponentiation to original (needed for invariant)
  ModPow(origB, origE, m);
  assert resNat == 1; // since m > 1, 1 % m == 1
  assert Exp_int(a, e) % m == Exp_int(origB, origE) % m;

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
      MulMod(oldRes * a, Exp_int(a, oldE - 1), m);
      assert resNat * Exp_int(a, e) % m == oldRes * Exp_int(a, oldE) % m;
    }
    if e > 0 {
      var oldA := a;
      var oldE := e;
      a := a * a % m;
      e := e / 2;
      // show invariant holds after squaring base and halving exponent
      PowDouble(oldA, oldE / 2);
      ModPow(oldA * oldA, oldE / 2, m);
      assert resNat * Exp_int(a, e) % m == resNat * Exp_int(oldA, oldE) % m;
    }
  }

  // Ensure we can build a binary string of length |sz| for resNat
  BitStringBound(sz);
  assert resNat < Exp_int(2, |sz|); // since resNat < m and m < 2^{|sz|}
  res := BuildBinary(|sz|, resNat);
}
// </vc-code>

