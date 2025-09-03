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

method DivMod(dividend: string, divisor: string) returns (quotient: string, remainder: string)
  requires ValidBitString(dividend) && ValidBitString(divisor)
  requires Str2Int(divisor) > 0
  ensures ValidBitString(quotient) && ValidBitString(remainder)
  ensures Str2Int(quotient) == Str2Int(dividend) / Str2Int(divisor)
  ensures Str2Int(remainder) == Str2Int(dividend) % Str2Int(divisor)
{
  assume{:axiom} false;
}

method Mul(s1: string, s2: string) returns (res: string)
  requires ValidBitString(s1) && ValidBitString(s2)
  ensures ValidBitString(res)
  ensures Str2Int(res) == Str2Int(s1) * Str2Int(s2)
{
  assume{:axiom} false;
}

// <vc-helpers>
function ExpNat(x: nat, y:nat): nat
{
  if y == 0 then 1 else x * ExpNat(x, y - 1)
}

function StrToNat(s: string): nat
  requires ValidBitString(s)
  decreases s
{
  if |s| == 0 then  0  else  (2 * StrToNat(s[0..|s|-1]) + (if s[|s|-1] == '1' then 1 else 0))
}

function Int2Str(k: nat): string
  ensures ValidBitString(Int2Str(k))
  ensures Str2Int(Int2Str(k)) == k
  decreases k
{
  if k == 0 then "" else Int2Str(k / 2) + (if k % 2 == 1 then "1" else "0")
}

lemma ExpNat_one(x: nat)
  ensures ExpNat(x,1) == x
{
  assert ExpNat(x,1) == x * ExpNat(x,0);
  assert ExpNat(x,0) == 1;
  assert x * 1 == x;
}

lemma ExpNat_add(x: nat, a: nat, b: nat)
  ensures ExpNat(x, a + b) == ExpNat(x, a) * ExpNat(x, b)
  decreases b
{
  if b == 0 {
    assert ExpNat(x, a + 0) == ExpNat(x, a) * ExpNat(x, 0);
  } else {
    ExpNat_add(x, a, b - 1);
    assert ExpNat(x, a + b) == if a + b == 0 then 1 else x * ExpNat(x, a + b - 1);
    assert ExpNat(x, b) == if b == 0 then 1 else x * ExpNat(x, b - 1);
    assert ExpNat(x, a) * ExpNat(x, b) == ExpNat(x, a) * (x * ExpNat(x, b - 1));
    assert ExpNat(x, a) * (x * ExpNat(x, b - 1)) == x * (ExpNat(x, a) * ExpNat(x, b - 1));
    assert x * (ExpNat(x, a) * ExpNat(x, b - 1)) == x * ExpNat(x, a + b - 1);
    assert x * ExpNat(x, a + b - 1) == ExpNat(x, a + b);
  }
}

lemma ExpNat_double(x: nat, e: nat)
  ensures ExpNat(x, 2 * e) == ExpNat(x, e) * ExpNat(x, e)
{
  ExpNat_add(x, e, e);
}

lemma ExpNat_eq_Exp_int(x: nat, y: nat)
  ensures ExpNat(x,y) == Exp_int(x,y)
  decreases y
{
  if y == 0 {
    assert ExpNat(x,0) == 1;
    assert Exp_int(x,0) == 1;
  } else {
    ExpNat_eq_Exp_int(x, y-1);
    assert ExpNat(x,y) == x * ExpNat(x,y-1);
    assert Exp_int(x,y) == x * Exp_int(x,y-1);
    assert ExpNat(x,y-1) == Exp_int(x,y-1);
  }
}

lemma StrToNat_eq_Str2Int(s: string)
  requires ValidBitString(s)
  ensures StrToNat(s) == Str2Int(s)
  decreases s
{
  if |s| == 0 {
    assert StrToNat(s) == 0;
    assert Str2Int(s) == 0;
  } else {
    StrToNat_eq_Str2Int(s[0..|s|-1]);
    var pref := s[0..|s|-1];
    assert StrToNat(s) == 2 * StrToNat(pref) + (if s[|s|-1] == '1' then 1 else 0);
    assert Str2Int(s) == 2 * Str2Int(pref) + (if s[|s|-1] == '1' then 1 else 0);
    assert StrToNat(pref) == Str2Int(pref);
  }
}

lemma ModMul(a: nat, m: nat)
  requires m > 0
  ensures ((a % m) * (a % m)) % m == (a * a) % m
{
  var q := a / m;
  var r := a % m;
  assert a == m * q + r;
  assert 0 <= r < m;
  // (m*q + r)*(m*q + r) = m*( ... ) + r*r, so (a*a) % m == (r*r) % m
  assert a * a == (m*q + r) * (m*q + r);
  assert (m*q + r) * (m*q + r) == m * (q*(m*q + r) + r*q) + r*r;
  assert (a*a) % m == (r*r) % m;
  assert r % m == r;
  assert (r*r) % m == ((r % m) * (r % m)) % m;
  assert ((a % m) * (a % m)) % m == (a * a) % m;
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
  var x := StrToNat(sx);
  var y := StrToNat(sy);
  var m := StrToNat(sz);
  StrToNat_eq_Str2Int(sx);
  StrToNat_eq_Str2Int(sy);
  StrToNat_eq_Str2Int(sz);
  assert x == Str2Int(sx);
  assert y == Str2Int(sy);
  assert m == Str2Int(sz);
  assert m > 1;

  if y == 0 {
    res := Int2Str(1 % m);
    assert Str2Int(res) == 1 % m;
    assert Exp_int(Str2Int(sx), Str2Int(sy)) == 1;
    assert Str2Int(res) == Exp_int(Str2Int(sx), Str2Int(sy)) % Str2Int(sz);
    return;
  }

  // y == 2^n
  var r := x % m;
  var i := 0;
  // invariant: 0 <= i <= n and r == ExpNat(x, ExpNat(2,i)) % m
  while i < n
    invariant 0 <= i <= n
    invariant r == ExpNat(x, ExpNat(2,i)) % m
  {
    var A := ExpNat(x, ExpNat(2,i));
    // next r is square modulo m
    var r2 := (r * r) % m;
    // use modular lemma to connect (A%A)^2 % m with (A*A) % m
    ModMul(A, m);
    assert r == A % m;
    assert r2 == (r * r) % m;
    assert r2 == ((A % m) * (A % m)) % m;
    assert r2 == (A * A) % m;
    // A * A == ExpNat(x, ExpNat(2,i) + ExpNat(2,i))
    assert A * A == ExpNat(x, ExpNat(2,i)) * ExpNat(x, ExpNat(2,i));
    assert ExpNat(x, ExpNat(2,i)) * ExpNat(x, ExpNat(2,i)) == ExpNat(x, ExpNat(2,i) + ExpNat(2,i));
    // ExpNat(2,i) + ExpNat(2,i) == 2 * ExpNat(2,i) == ExpNat(2,i+1)
    assert ExpNat(2, i + 1) == 2 * ExpNat(2, i);
    assert ExpNat(2, i) + ExpNat(2, i) == 2 * ExpNat(2, i);
    assert ExpNat(2, i) + ExpNat(2, i) == ExpNat(2, i + 1);
    assert ExpNat(x, ExpNat(2,i) + ExpNat(2,i)) == ExpNat(x, ExpNat(2, i + 1));
    // combine to get the new invariant
    r := r2;
    i := i + 1;
  }

  // after loop, i == n and r == ExpNat(x, ExpNat(2,n)) % m
  res := Int2Str(r);
  assert Str2Int(res) == r;

  // relate to Exp_int forms
  ExpNat_eq_Exp_int(x, ExpNat(2, n));
  ExpNat_eq_Exp_int(2, n);
  assert ExpNat(x, ExpNat(2,n)) == Exp_int(x, ExpNat(2,n));
  assert ExpNat(2,n) == Exp_int(2,n);
  // y equals ExpNat(2,n) (since StrToNat(sy) satisfied precondition)
  assert y == ExpNat(2,n);
  assert Exp_int(x, y) == Exp_int(x, ExpNat(2,n));
  assert Exp_int(x, ExpNat(2,n)) == ExpNat(x, ExpNat(2,n));
  // connect x,y,m with Str2Int versions
  assert x == Str2Int(sx);
  assert y == Str2Int(sy);
  assert m == Str2Int(sz);
  assert Str2Int(res) == Exp_int(Str2Int(sx), Str2Int(sy)) % Str2Int(sz);
}
// </vc-code>

