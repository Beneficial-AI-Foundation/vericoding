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

// <vc-helpers>
function BitsToNat(s: string): nat
  requires ValidBitString(s)
  decreases s
{
  if |s| == 0 then 0 else 2 * BitsToNat(s[0..|s|-1]) + (if s[|s|-1] == '1' then 1 else 0)
}

lemma BitsToNat_Str2Int(s: string)
  requires ValidBitString(s)
  ensures BitsToNat(s) == Str2Int(s)
  decreases s
{
  if |s| == 0 {
    assert BitsToNat(s) == 0;
    assert Str2Int(s) == 0;
  } else {
    BitsToNat_Str2Int(s[0..|s|-1]);
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
  var m := BitsToNat(sz);
  if BitsToNat(sy) == 0 {
    res := NatToBin(1 % m);
    NatToBin_spec(1 % m);
    // connect BitsToNat and Str2Int for postcondition reasoning
    BitsToNat_Str2Int(sx);
    BitsToNat_Str2Int(sy);
    BitsToNat_Str2Int(sz);
    return;
  }
  var acc := BitsToNat(sx) % m;
  var i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant acc == Exp_int(BitsToNat(sx), Exp_int(2, i)) % m
  {
    var oldAcc := acc;
    var oldI := i;
    var newAcc := (oldAcc * oldAcc) % m;
    i := i + 1;
    assert oldAcc == Exp_int(BitsToNat(sx), Exp_int(2, oldI)) % m;
    var p := Exp_int(2, oldI);
    var e := Exp_int(BitsToNat(sx), p);
    assert oldAcc == e % m;
    assert newAcc == (oldAcc * oldAcc) % m;
    assert (oldAcc * oldAcc) % m == ((e % m) * (e % m)) % m;
    ModMul(e, e, m);
    assert ((e % m) * (e % m)) % m == (e * e) % m;
    Exp2_succ(oldI);
    Exp_int_mul(BitsToNat(sx), p, p);
    assert e * e == Exp_int(BitsToNat(sx), p + p);
    assert p + p == Exp_int(2, i);
    assert (e * e) % m == Exp_int(BitsToNat(sx), Exp_int(2, i)) % m;
    assert newAcc == Exp_int(BitsToNat(sx), Exp_int(2, i)) % m;
    acc := newAcc;
  }
  res := NatToBin(acc);
  NatToBin_spec(acc);
  BitsToNat_Str2Int(sx);
  BitsToNat_Str2Int(sy);
  BitsToNat_Str2Int(sz);
}
// </vc-code>

