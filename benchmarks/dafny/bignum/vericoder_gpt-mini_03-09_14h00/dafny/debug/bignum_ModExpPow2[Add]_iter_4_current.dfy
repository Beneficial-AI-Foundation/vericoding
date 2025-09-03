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
  decreases n
{
  if n == 0 then "" else NatToBin(n / 2) + (if n % 2 == 1 then "1" else "0")
}

lemma NatToBin_spec(n: nat)
  ensures ValidBitString(NatToBin(n))
  ensures Str2Int(NatToBin(n)) == n
  decreases n
{
  if n == 0 {
    // NatToBin(0) == "" and Str2Int("") == 0
  } else {
    var q := n / 2;
    var r := n % 2;
    NatToBin_spec(q);
    // NatToBin(n) = NatToBin(q) + bit, and Str2Int concatenation gives 2*Str2Int(NatToBin(q)) + r
    assert ValidBitString(NatToBin(q));
    assert Str2Int(NatToBin(q)) == q;
    var s := NatToBin(q) + (if r == 1 then "1" else "0");
    assert ValidBitString(s);
    assert Str2Int(s) == 2 * Str2Int(NatToBin(q)) + r;
    assert 2 * Str2Int(NatToBin(q)) + r == 2 * q + r;
    assert 2 * q + r == n;
  }
}

lemma ModMul(a: nat, b: nat, m: nat)
  requires m > 0
  ensures ((a % m) * (b % m)) % m == (a * b) % m
{
  var r1 := a % m;
  var r2 := b % m;
  var q1 := a / m;
  var q2 := b / m;
  assert a == q1 * m + r1;
  assert b == q2 * m + r2;
  var t := a * b - r1 * r2;
  calc {
    t;
    == { }
    (q1 * m + r1) * (q2 * m + r2) - r1 * r2;
    == { }
    q1 * q2 * m * m + q1 * m * r2 + q2 * m * r1;
    == { }
    m * (q1 * q2 * m + q1 * r2 + q2 * r1);
  }
  // t is divisible by m, so t % m == 0, hence (a*b) % m == (r1*r2) % m
  assert t % m == 0;
  assert (a * b) % m == (r1 * r2) % m;
  assert (r1 * r2) % m == ((a % m) * (b % m)) % m;
}

lemma Exp2_succ(i: nat)
  ensures Exp_int(2, i) + Exp_int(2, i) == Exp_int(2, i + 1)
  decreases i
{
  // By definition Exp_int(2, i+1) = 2 * Exp_int(2, i)
  assert Exp_int(2, i + 1) == 2 * Exp_int(2, i);
  assert Exp_int(2, i) + Exp_int(2, i) == 2 * Exp_int(2, i);
}

lemma Exp_int_mul(x: nat, p: nat, q: nat)
  ensures Exp_int(x, p) * Exp_int(x, q) == Exp_int(x, p + q)
  decreases q
{
  if q == 0 {
    assert Exp_int(x, q) == 1;
    assert Exp_int(x, p + q) == Exp_int(x, p);
  } else {
    Exp_int_mul(x, p, q - 1);
    // Exp_int(x, p + q) = x * Exp_int(x, p + q - 1)
    assert Exp_int(x, p + q) == x * Exp_int(x, p + q - 1);
    assert Exp_int(x, p + q - 1) == Exp_int(x, p) * Exp_int(x, q - 1);
    assert x * Exp_int(x, p + q - 1) == Exp_int(x, p) * (x * Exp_int(x, q - 1));
    assert x * Exp_int(x, q - 1) == Exp_int(x, q);
    assert Exp_int(x, p) * Exp_int(x, q) == Exp_int(x, p + q);
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
  if IntOf(sy) == 0 {
    IntOf_eq_Str2Int(sy);
    IntOf_eq_Str2Int(sz);
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
  IntOf_eq_Str2Int(sz);
  NatToBin_spec(acc);
  res := NatToBin(acc);
}
// </vc-code>

