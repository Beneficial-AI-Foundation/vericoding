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
method NatToBits(n_in: nat) returns (s: string)
  ensures ValidBitString(s)
  ensures Str2Int(s) == n_in
{
  if n_in == 0 {
    s := "0";
    return;
  }

  var rem := n_in;
  s := "";
  while rem > 0
    invariant 0 <= rem <= n_in
    invariant ValidBitString(s)
    invariant Str2Int(s) + rem * Exp_int(2, |s|) == n_in
    decreases rem
  {
    var old_rem := rem;
    var bit := old_rem % 2;
    if bit == 1 {
      s := "1" + s;
    } else {
      s := "0" + s;
    }
    rem := old_rem / 2;
    // use division property for base 2
    Div2(old_rem);
    assert old_rem == 2 * rem + bit;
    // Maintain invariant:
    // Str2Int(s) = bit * Exp_int(2, |s|-1) + Str2Int(s[1..])
    // The algebra follows from the division equation above and the previous invariant.
  }
  assert rem == 0;
  assert Str2Int(s) == n_in;
}

lemma Div2(n: nat)
  ensures n == 2*(n/2) + n%2 && n%2 < 2
{
  var q := n/2;
  var r := n%2;
  assert n == q*2 + r;
  assert r < 2;
}

lemma DivMul(k: nat, m: nat)
  requires m > 0
  ensures (k*m) / m == k && (k*m) % m == 0
{
  var q := (k*m) / m;
  var r := (k*m) % m;
  assert (k*m) == q*m + r;
  assert (k*m) - q*m == r;
  assert k*m - q*m == (k - q) * m;
  assert r < m;
  assert (k - q) * m == r;
  if m > 0 {
    if k != q {
      assert (k - q) * m >= m;
    }
    assert k == q;
    assert r == 0;
  }
  assert (k*m) / m == k;
  assert (k*m) % m == 0;
}

lemma MulMod(x: nat, y: nat, m: nat)
  requires m > 0
  ensures (x * y) % m == ((x % m) * y) % m
{
  var q := x / m;
  var r := x % m;
  assert x == q*m + r;
  assert x * y == q*m*y + r*y;
  var k := q*y;
  assert q*m*y == k*m;
  DivMul(k, m);
  assert (q*m*y + r*y) % m == (r*y) % m;
  assert (x * y) % m == (r*y) % m;
  assert r == x % m;
  assert (r*y) % m == ((x % m) * y) % m;
}

lemma Exp_step(x: nat, y: nat)
  ensures Exp_int(x, y + 1) == Exp_int(x, y) * x
  decreases y
{
  if y == 0 {
    assert Exp_int(x, 1) == x;
    assert Exp_int(x, 0) == 1;
  } else {
    Exp_step(x, y - 1);
  }
  assert Exp_int(x, y + 1) == x * Exp_int(x, y);
  assert x * Exp_int(x, y) == Exp_int(x, y) * x;
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
  var base := Str2Int(sx);
  var exp := Str2Int(sy);
  var m := Str2Int(sz);

  assert m > 1;
  // initialize
  var resNat := 1 % m;
  var i := 0;
  var origExp := exp;

  // help the verifier with initial facts
  assert Exp_int(base, 0) == 1;
  assert resNat == 1 % m;
  assert resNat == Exp_int(base, 0) % m;
  assert 0 <= resNat < m;

  while i < origExp
    invariant 0 <= i <= origExp
    invariant 0 <= resNat < m
    invariant resNat == Exp_int(base, i) % m
    decreases origExp - i
  {
    var old_i := i;
    var old_res := resNat;

    // update
    resNat := (old_res * base) % m;
    i := i + 1;

    // proof that invariant holds for new i
    assert 0 <= old_res < m;
    assert old_res == Exp_int(base, old_i) % m;

    Exp_step(base, old_i);
    MulMod(Exp_int(base, old_i), base, m);

    assert (Exp_int(base, old_i + 1) % m) == ((Exp_int(base, old_i) % m) * base) % m;
    assert ((Exp_int(base, old_i) % m) * base) % m == (old_res * base) % m;
    assert resNat == Exp_int(base, i) % m;
  }

  res := NatToBits(resNat);
}
// </vc-code>

