```vc-helpers
method NatToBits(n: nat) returns (s: string)
  ensures ValidBitString(s)
  ensures Str2Int(s) == n
  decreases n
{
  if n == 0 {
    s := "0";
  } else {
    var q := n / 2;
    var r := n % 2;
    var qbits := NatToBits(q);
    if r == 0 {
      s := qbits + "0";
    } else {
      s := qbits + "1";
    }
  }
}

lemma Exp_add(x: nat, e1: nat, e2: nat)
  ensures Exp_int(x, e1 + e2) == Exp_int(x, e1) * Exp_int(x, e2)
  decreases e2
{
  if e2 == 0 {
    assert Exp_int(x, e1 + 0) == Exp_int(x, e1);
    assert Exp_int(x, 0) == 1;
    assert Exp_int(x, e1) == Exp_int(x, e1) * 1;
  } else {
    Exp_add(x, e1, e2 - 1);
    assert Exp_int(x, e1 + e2) == x * Exp_int(x, e1 + e2 - 1);
    assert Exp_int(x, e1 + e2 - 1) == Exp_int(x, e1) * Exp_int(x, e2 - 1);
    assert x * (Exp_int(x, e1) * Exp_int(x, e2 - 1)) == Exp_int(x, e1) * (x * Exp_int(x, e2 - 1));
    assert x * Exp_int(x, e2 - 1) == Exp_int(x, e2);
    assert Exp_int(x, e1 + e2) == Exp_int(x, e1) * Exp_int(x, e2);
  }
}

lemma ModMulCongruence(a: nat, b: nat, m: nat)
  requires m > 0
  ensures (a % m) * (b % m) % m == (a * b) % m
{
  var r := a % m;
  var q := a / m;
  var s := b % m;
  var t := b / m;
  // a = m*q + r, b = m*t + s
  assert a == m * q + r;
  assert b == m * t + s;
  // Multiply out
  assert a * b == m * (m * q * t + q * s + t * r) + r * s;
  // Modulo m ignores the multiple of m part
  assert (a * b) % m == (r * s) % m;
  // And r == a % m and s == b % m
  assert r == a % m;
  assert s == b % m;
  assert (r * s) % m == ((a % m) * (b % m)) % m;
}

lemma ModMulExp(x: nat, e1: nat, e2: nat, m: nat)
  requires m > 0
  ensures (Exp_int(x, e1) % m) * (Exp_int(x, e2) % m) % m == Exp_int(x, e1 + e2) % m
{
  // By Exp_add: Exp_int(x, e1+e2) = Exp_int(x,e1) * Exp_int(x,e2)
  Exp_add(x, e1, e2);
  // Then apply ModMulCongruence to the product
  ModMulCongruence(Exp_int(x, e1), Exp_int(x, e2), m);
  assert (Exp_int(x, e1) * Exp_int(x, e2)) % m == Exp_int(x, e1 + e2) % m;
  assert ((Exp_int(x, e1) % m) * (Exp_int(x, e2) % m)) % m == (Exp_int(x, e1) * Exp_int(x, e2)) % m;
}

lemma Exp_double(j: nat)
  ensures Exp_int(2, j + 1) == 2 * Exp_int(2, j)
  decreases j
{
  if j == 0 {
    assert Exp_int(2, 1) == 2;
    assert Exp_int(2, 0) == 1;
    assert 2 * Exp_int(2, 0) == 2;
  } else {
    Exp_double(j - 1);
    // By definition Exp_int(2, j+1) = 2 * Exp_int(2, j)
    assert Exp_int(2, j + 1) == 2 * Exp_int(2, j);
  }
}

lemma PrefixBit(c: char, t: string)
  requires c == '0' || c == '1'
  requires ValidBitString(t)
  ensures Str2Int((if c == '1' then "1" else "0") + t) == Str2Int(t) + (if c == '1' then Exp_int(2, |t|) else 0)
  decreases |t|
{
  if |t| == 0 {
    // Left is "0" or "1", right is 0 + bit*c * 1
  } else {
    var u := t[0..|t|-1];
    var last := t[|t|-1];
    // Str2Int((c) + t) = 2*Str2Int((c)+u) + bit(last)
    // Str2Int(t) = 2*Str2Int(u) + bit(last)
    PrefixBit(c, u);
    assert Str