```vc-helpers
function Nat2Str(x: nat): string
  ensures ValidBitString(Nat2Str(x))
  ensures Str2Int(Nat2Str(x)) == x
  decreases x
{
  if x == 0 then "" else
    var q := x / 2;
    var r := x % 2;
    Nat2Str(q) + (if r == 1 then "1" else "0")
}

lemma {:axiom} MulMod(a: nat, b: nat, m: nat)
  requires m > 0
  ensures (a % m * b % m) % m == (a * b) % m
{
}

lemma Exp_int_add_mul(x: nat, a: nat, b: nat)
  ensures Exp_int(x, a) * Exp_int(x, b) == Exp_int(x, a + b)
  decreases b
{
  if b == 0 {
    assert Exp_int(x, b) == 1;
    assert Exp_int(x, a) * 1 == Exp_int(x, a + 0);
  } else {
    Exp_int_add_mul(x, a, b - 1);
    // Exp_int(x, b) == x * Exp_int(x, b-1) by definition
    assert Exp_int(x, b) == x * Exp_int(x, b - 1);
    calc {
      Exp_int(x, a) * Exp_int(x, b);
      == Exp_int(x, a) * (x * Exp_int(x, b - 1));
      == x * (Exp_int(x, a) * Exp_int(x, b - 1));
      == x * Exp_int(x, a + b - 1);
      == Exp_int(x, a + b);
    }
  }
}

lemma Str2Int_prefix(s: string, i: int)
  requires ValidBitString(s)
  requires 0 <= i < |s|
  ensures Str2Int(s[0..i+1]) == 2 * Str2Int(s[0..i]) + (if s[i] == '1' then 1 else 0)
{
  var t := s[0..i+1];
  assert t[0..i] == s[0..i];
  assert t[i] == s[i];
  if |t| == 0 {
    // impossible because i >= 0
  } else {
    // By definition of Str2Int on non-empty string t:
    assert Str2Int(t) == 2 * Str2Int(t[0..|t|-1]) + (if t[|t|-1] == '1' then 1 else 0);
    assert |t|-1 == i;
    assert Str2Int(t) == 2 * Str2Int(t[0..i]) + (if t[i] == '1' then 1 else 0);
    assert Str2Int(t) == 2 * Str2Int(s[0..i]) + (if s[i] == '1' then 1 else 0);
  }
}

method BitsToNat(s: string) returns (x: nat)
  requires ValidBitString(s)
  ensures x == Str2Int(s)
  decreases s
{
  x := 0;
  var i := 0;
  while i < |s|
    invariant 0 <= i <= |s|
    invariant x == Str2Int(s[0..i])
  {
    var bit := (if s[i] == '1' then 1 else 0);
    x := 2 * x + bit;
    // Prove the invariant for i+1
    Str2Int_prefix(s, i);
    assert x == Str2Int(s[0..i+1]);
    i := i + 1;
  }
}
```

```vc-code
{
  var base := BitsToNat(sx);
  var modulo := BitsToNat(sz);
  var r: nat := 1;
  var i := 0;
  // Process bits from most-significant (index 0) to least-significant (index |sy|-1)
  while i < |sy|
    invariant 0 <= i <= |sy|
    invariant r == Exp_int(base, Str2Int(sy[0..i])) % modulo
  {
    var p := Str2Int(sy[0..i]);
    var oldr := r;
    r := (oldr * oldr) % modulo;
    assert oldr == Exp_int(base, p) % modulo;
    assert r == (Exp_int(base, p) % modulo * Exp_int(base, p) % modulo) % modulo;
    MulMod(Exp_int(base, p), Exp_int(base, p), modulo);
    assert r == (Exp_int(base, p) * Exp_int(base, p)) % modulo;
    Exp_int_add_mul(base, p, p);
    assert r == Exp_int(base, 2 * p) % modulo;
    if sy[i] == '1' {
      var oldr2 := r;
      r := (oldr2 * base) % modulo;
      assert oldr2 == Exp_int(base, 2 * p) % modulo;
      assert r == (Exp_int(base, 2 * p) % modulo * base % modulo) % modulo;
      MulMod(Exp_int(base, 2 * p), base, modulo);
      assert r == (Exp_int(base, 2 * p) * base) % modulo;
      assert Exp_int(base, 2 * p + 1) == base * Exp_int(base, 2 * p);
      assert r == Exp_int(base, 2 * p + 1) % modulo;
    }
    Str2Int_prefix(sy, i);
    assert Str2Int(sy[0..i+1]) == 2 * p + (if sy[i] == '1' then 1 else 0);
    assert r == Exp_int(base, Str2Int(sy[0..i+1])) % modulo;
    i := i + 1;
  }
  res := Nat2Str(r);
}
```