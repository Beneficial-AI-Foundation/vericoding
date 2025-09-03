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

function NatToBin(x: nat): string
  decreases x
{
  if x == 0 then "" else
    var q := x / 2;
    var r := x % 2;
    NatToBin(q) + (if r == 1 then "1" else "0")
}

lemma NatToBin_spec(x: nat)
  ensures ValidBitString(NatToBin(x)) && BitsToNat(NatToBin(x)) == x
  decreases x
{
  if x == 0 {
    assert NatToBin(0) == "";
    assert ValidBitString("");
    assert BitsToNat("") == 0;
  } else {
    var q := x / 2;
    var r := x % 2;
    assert x == q * 2 + r;
    NatToBin_spec(q);
    var s := NatToBin(q);
    var t := if r == 1 then "1" else "0";
    // s is valid bitstring by induction, t is "0" or "1"
    assert ValidBitString(s);
    assert ValidBitString(t);
    assert ValidBitString(s + t);
    // use definition of BitsToNat on concatenation where last char is t[0]
    assert (s + t)[0..|s + t| - 1] == s;
    assert (s + t)[|s + t| - 1] == t[0];
    assert BitsToNat(s + t) == 2 * BitsToNat(s) + (if t[0] == '1' then 1 else 0);
    assert (if t[0] == '1' then 1 else 0) == r;
    assert BitsToNat(s) == q;
    assert BitsToNat(NatToBin(q) + t) == q * 2 + r;
    assert BitsToNat(NatToBin(q) + t) == x;
  }
}

lemma ModMul(a: nat, b: nat, m: nat)
  requires m > 0
  ensures ((a % m) * (b % m)) % m == (a * b) % m
{
  var q1 := a / m; var r1 := a % m;
  var q2 := b / m; var r2 := b % m;
  assert a == q1 * m + r1;
  assert b == q2 * m + r2;
  assert a * b == (q1 * m + r1) * (q2 * m + r2);
  assert (q1 * m + r1) * (q2 * m + r2) == q1*q2*m*m + q1*m*r2 + q2*m*r1 + r1*r2;
  // All terms except r1*r2 are multiples of m, so (a*b) % m == (r1*r2) % m
  assert (a * b) % m == (r1 * r2) % m;
  assert ((a % m) * (b % m)) % m == (r1 * r2) % m;
}

lemma Exp2_succ(k: nat)
  ensures Exp_int(2, k) + Exp_int(2, k) == Exp_int(2, k + 1)
  decreases k
{
  if k == 0 {
    assert Exp_int(2,0) == 1;
    assert Exp_int(2,1) == 2;
    assert Exp_int(2,0) + Exp_int(2,0) == Exp_int(2,1);
  } else {
    // Exp_int(2,k+1) == 2 * Exp_int(2,k) by definition
    assert Exp_int(2,k+1) == 2 * Exp_int(2,k);
    assert Exp_int(2,k) + Exp_int(2,k) == 2 * Exp_int(2,k);
  }
}

lemma Exp_int_mul(x: nat, a: nat, b: nat)
  ensures Exp_int(x,a) * Exp_int(x,b) == Exp_int(x, a + b)
  decreases b
{
  if b == 0 {
    assert Exp_int(x,0) == 1;
    assert Exp_int(x,a) * Exp_int(x,0) == Exp_int(x,a);
    assert Exp_int(x,a) == Exp_int(x, a + 0);
  } else {
    Exp_int_mul(x, a, b - 1);
    assert Exp_int(x,b) == x * Exp_int(x, b - 1);
    assert Exp_int(x,a) * Exp_int(x,b) == Exp_int(x,a) * (x * Exp_int(x,b-1));
    assert Exp_int(x,a) * (x * Exp_int(x,b-1)) == x * (Exp_int(x,a) * Exp_int(x,b-1));
    assert Exp_int(x,a) * Exp_int(x,b-1) == Exp_int(x, a + (b - 1));
    assert x * Exp_int(x, a + (b - 1)) == Exp_int(x, a + b);
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

