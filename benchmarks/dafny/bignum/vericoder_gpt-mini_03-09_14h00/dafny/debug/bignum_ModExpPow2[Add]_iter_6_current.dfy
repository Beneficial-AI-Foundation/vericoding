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
function IntOf(s: string): nat
  requires ValidBitString(s)
  decreases s
{
  if |s| == 0 then 0 else 2 * IntOf(s[0..|s|-1]) + (if s[|s|-1] == '1' then 1 else 0)
}

lemma IntOf_eq_Str2Int(s: string)
  requires ValidBitString(s)
  ensures IntOf(s) == Str2Int(s)
  decreases s
{
  if |s| == 0 {
  } else {
    IntOf_eq_Str2Int(s[0..|s|-1]);
    assert IntOf(s) == 2 * IntOf(s[0..|s|-1]) + (if s[|s|-1] == '1' then 1 else 0);
    assert Str2Int(s) == 2 * Str2Int(s[0..|s|-1]) + (if s[|s|-1] == '1' then 1 else 0);
    assert IntOf(s[0..|s|-1]) == Str2Int(s[0..|s|-1]);
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
  var m := IntOf(sz);
  IntOf_eq_Str2Int(sz);
  if IntOf(sy) == 0 {
    IntOf_eq_Str2Int(sy);
    NatToBin_spec(1 % m);
    res := NatToBin(1 % m);
    return;
  }
  var acc := IntOf(sx) % m;
  var i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant acc == Exp_int(IntOf(sx), Exp_int(2, i)) % m
  {
    var oldAcc := acc;
    var oldI := i;
    var newAcc := (oldAcc * oldAcc) % m;
    i := i + 1;
    assert oldAcc == Exp_int(IntOf(sx), Exp_int(2, oldI)) % m;
    var p := Exp_int(2, oldI);
    var e := Exp_int(IntOf(sx), p);
    assert oldAcc == e % m;
    assert newAcc == (oldAcc * oldAcc) % m;
    assert (oldAcc * oldAcc) % m == ((e % m) * (e % m)) % m;
    ModMul(e, e, m);
    assert ((e % m) * (e % m)) % m == (e * e) % m;
    Exp2_succ(oldI);
    Exp_int_mul(IntOf(sx), p, p);
    assert e * e == Exp_int(IntOf(sx), p + p);
    assert p + p == Exp_int(2, i);
    assert (e * e) % m == Exp_int(IntOf(sx), Exp_int(2, i)) % m;
    assert newAcc == Exp_int(IntOf(sx), Exp_int(2, i)) % m;
    acc := newAcc;
  }
  IntOf_eq_Str2Int(sx);
  IntOf_eq_Str2Int(sy);
  NatToBin_spec(acc);
  res := NatToBin(acc);
}
// </vc-code>

