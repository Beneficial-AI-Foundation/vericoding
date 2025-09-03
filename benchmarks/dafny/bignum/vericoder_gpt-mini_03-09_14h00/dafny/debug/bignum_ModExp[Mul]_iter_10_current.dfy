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

method Mul(s1: string, s2: string) returns (res: string)
  requires ValidBitString(s1) && ValidBitString(s2)
  ensures ValidBitString(res)
  ensures Str2Int(res) == Str2Int(s1) * Str2Int(s2)
{
  assume{:axiom} false;
}

// <vc-helpers>
method BitsToNat(s: string) returns (n: nat)
  requires ValidBitString(s)
  ensures n == Str2Int(s)
{
  n := 0;
  var i := 0;
  while i < |s|
    invariant 0 <= i <= |s|
    invariant 0 <= n
    invariant n == Str2Int(s[0..i])
    decreases |s| - i
  {
    var bit := if s[i] == '1' then 1 else 0;
    // Prove relation for the ghost function Str2Int on the extended prefix
    ghost {
      // By definition of Str2Int on a non-empty string:
      assert Str2Int(s[0..i+1]) == 2 * Str2Int(s[0..i]) + (if s[i] == '1' then 1 else 0);
      assert (if s[i] == '1' then 1 else 0) == bit;
    }
    n := 2 * n + bit;
    i := i + 1;
    ghost {
      // Maintain the invariant n == Str2Int(s[0..i])
      assert n == Str2Int(s[0..i]);
    }
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
  var base := BitsToNat(sx);
  var exp := BitsToNat(sy);
  var m := BitsToNat(sz);

  assert m > 1;
  // initialize
  var resNat := 1 % m;
  var i := 0;
  var origExp := exp;

  // ghost proofs of initial facts
  ghost {
    assert Exp_int(base, 0) == 1;
    assert resNat == Exp_int(base, 0) % m;
    assert 0 <= resNat < m;
  }

  while i < origExp
    invariant 0 <= i <= origExp
    invariant 0 <= resNat < m
    invariant resNat == Exp_int(base, i) % m
    decreases origExp - i
  {
    var old_i := i;
    var old_res := resNat;

    // update (non-ghost)
    resNat := (old_res * base) % m;
    i := i + 1;

    // ghost-only proof that invariant holds after update
    ghost {
      assert 0 <= old_res < m;
      assert old_res == Exp_int(base, old_i) % m;

      Exp_step(base, old_i);
      MulMod(Exp_int(base, old_i), base, m);

      assert (Exp_int(base, old_i + 1) % m) == ((Exp_int(base, old_i) % m) * base) % m;
      assert ((Exp_int(base, old_i) % m) * base) % m == (old_res * base) % m;
      assert resNat == Exp_int(base, i) % m;
    }
  }

  res := NatToBits(resNat);
}
// </vc-code>

