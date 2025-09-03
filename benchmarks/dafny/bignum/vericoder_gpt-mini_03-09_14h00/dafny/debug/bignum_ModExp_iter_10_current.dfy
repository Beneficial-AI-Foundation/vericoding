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

// <vc-helpers>
lemma MulMod(x: nat, y: nat, m: nat)
  requires m > 0
  ensures (x * y) % m == ((x % m) * (y % m)) % m
{
  var xm := x % m;
  var xq := x / m;
  var ym := y % m;
  var yq := y / m;
  assert x == xm + m * xq;
  assert y == ym + m * yq;
  assert x * y == (xm + m * xq) * (ym + m * yq);
  assert x * y == xm * ym + m * (xm * yq + xq * ym + m * xq * yq);
  assert (x * y) % m == (xm * ym) % m;
  assert ((x % m) * (y % m)) % m == (xm * ym) % m;
}

lemma Exp_add(b: nat, n: nat, m: nat)
  ensures Exp_int(b, n + m) == Exp_int(b, n) * Exp_int(b, m)
  decreases m
{
  if m == 0 {
    assert n + 0 == n;
    assert Exp_int(b, n + 0) == Exp_int(b, n);
    assert Exp_int(b, 0) == 1;
    assert Exp_int(b, n) * Exp_int(b, 0) == Exp_int(b, n);
  } else {
    Exp_add(b, n, m - 1);
    // Exp_int(b, n + m) = b * Exp_int(b, n + m - 1)
    assert Exp_int(b, n + m) == b * Exp_int(b, n + m - 1);
    // By induction hypothesis: Exp_int(b, n + m - 1) == Exp_int(b, n) * Exp_int(b, m - 1)
    assert Exp_int(b, n + m - 1) == Exp_int(b, n) * Exp_int(b, m - 1);
    // So Exp_int(b, n + m) == b * (Exp_int(b, n) * Exp_int(b, m - 1))
    assert Exp_int(b, n + m) == b * (Exp_int(b, n) * Exp_int(b, m - 1));
    // Rearrange: b * (Exp_int(b, n) * Exp_int(b, m - 1)) == Exp_int(b, n) * (b * Exp_int(b, m - 1))
    assert Exp_int(b, n + m) == Exp_int(b, n) * (b * Exp_int(b, m - 1));
    // But b * Exp_int(b, m - 1) == Exp_int(b, m)
    assert b * Exp_int(b, m - 1) == Exp_int(b, m);
    assert Exp_int(b, n + m) == Exp_int(b, n) * Exp_int(b, m);
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
  var m := Str2Int(sz);
  var bfull := Str2Int(sx);
  var base := bfull % m;
  var resNat := 1 % m;
  var i := 0;
  while i < |sy|
    invariant 0 <= i <= |sy|
    invariant resNat == Exp_int(bfull, Str2Int(sy[0..i])) % m
    invariant m > 0
    invariant base == bfull % m
  {
    var prefix := Str2Int(sy[0..i]);
    // square step: compute (resNat * resNat) % m
    var sq := (resNat * resNat) % m;
    // Show sq corresponds to Exp_int(bfull, 2*prefix) % m
    Exp_add(bfull, prefix, prefix);
    assert Exp_int(bfull, 2 * prefix) == Exp_int(bfull, prefix) * Exp_int(bfull, prefix);
    MulMod(Exp_int(bfull, prefix), Exp_int(bfull, prefix), m);
    // Relate sq to multiplication of raw powers
    assert sq == ((Exp_int(bfull, prefix) % m) * (Exp_int(bfull, prefix) % m)) % m;
    assert ((Exp_int(bfull, prefix) % m) * (Exp_int(bfull, prefix) % m)) % m == (Exp_int(bfull, prefix) * Exp_int(bfull, prefix)) % m;
    assert (Exp_int(bfull, prefix) * Exp_int(bfull, prefix)) % m == Exp_int(bfull, 2 * prefix) % m;
    assert sq == Exp_int(bfull, 2 * prefix) % m;
    var newRes := sq;
    if sy[i] == '1' {
      newRes := (newRes * base) % m;
      // Show newRes == Exp_int(bfull, 2*prefix + 1) % m
      Exp_add(bfull, 2 * prefix, 1);
      assert Exp_int(bfull, 2 * prefix + 1) == Exp_int(bfull, 2 * prefix) * Exp_int(bfull, 1);
      assert Exp_int(bfull, 1) == bfull;
      // Relate modulus multiplication
      MulMod(Exp_int(bfull, 2 * prefix), bfull, m);
      assert ((Exp_int(bfull, 2 * prefix) % m) * (bfull % m)) % m == (Exp_int(bfull, 2 * prefix) * bfull) % m;
      assert (Exp_int(bfull, 2 * prefix) * bfull) % m == Exp_int(bfull, 2 * prefix + 1) % m;
      // combine with sq == Exp_int(... ) % m and base == bfull % m
      assert newRes == ((Exp_int(bfull, 2 * prefix) % m) * (bfull % m)) % m;
      assert newRes == Exp_int(bfull, 2 * prefix + 1) % m;
    } else {
      assert newRes == Exp_int(bfull, 2 * prefix) % m;
    }
    resNat := newRes;
    i := i + 1;
  }
  res := Int2Str(resNat);
}
// </vc-code>

