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
function NatToBin(n: nat): string
  ensures ValidBitString(NatToBin(n))
  ensures Str2Int(NatToBin(n)) == n
  decreases n
{
  if n == 0 then "" else
    var t := NatToBin(n / 2);
    if n % 2 == 1 then t + "1" else t + "0"
}

lemma Exp_int_mul(x: nat, p: nat, q: nat)
  ensures Exp_int(x, p) * Exp_int(x, q) == Exp_int(x, p + q)
  decreases q
{
  if q == 0 {
  } else {
    Exp_int_mul(x, p, q - 1);
  }
}

lemma Exp2_succ(i: nat)
  ensures Exp_int(2, i + 1) == 2 * Exp_int(2, i)
  decreases i
{
  if i == 0 {
  } else {
    Exp2_succ(i - 1);
  }
}

lemma ModMul(a: nat, b: nat, m: nat)
  ensures ((a % m) * (b % m)) % m == (a * b) % m
{
  var ra := a % m;
  var qa := a / m;
  var rb := b % m;
  var qb := b / m;
  assert a == ra + qa * m;
  assert b == rb + qb * m;
  assert a * b == ra * rb + m * (ra * qb + rb * qa + m * qa * qb);
  assert (a * b) % m == (ra * rb) % m;
  assert ((a % m) * (b % m)) % m == (ra * rb) % m;
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
  var m := Str2Int(sz);
  if Str2Int(sy) == 0 {
    res := NatToBin(1 % m);
    return;
  }
  var acc := (Str2Int(sx) % m);
  var i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant acc == Exp_int(Str2Int(sx), Exp_int(2, i)) % m
  {
    var oldAcc := acc;
    var oldI := i;
    var newAcc := (oldAcc * oldAcc) % m;
    i := i + 1;
    // Proof that newAcc == Exp_int(Str2Int(sx), Exp_int(2, i)) % m
    assert oldAcc == Exp_int(Str2Int(sx), Exp_int(2, oldI)) % m;
    var p := Exp_int(2, oldI);
    var e := Exp_int(Str2Int(sx), p);
    assert oldAcc == e % m;
    assert newAcc == (oldAcc * oldAcc) % m;
    assert (oldAcc * oldAcc) % m == ((e % m) * (e % m)) % m;
    ModMul(e, e, m);
    assert ((e % m) * (e % m)) % m == (e * e) % m;
    Exp2_succ(oldI);
    Exp_int_mul(Str2Int(sx), p, p);
    assert e * e == Exp_int(Str2Int(sx), p + p);
    assert p + p == Exp_int(2, i);
    assert (e * e) % m == Exp_int(Str2Int(sx), Exp_int(2, i)) % m;
    assert newAcc == Exp_int(Str2Int(sx), Exp_int(2, i)) % m;
    acc := newAcc;
  }
  res := NatToBin(acc);
}
// </vc-code>

