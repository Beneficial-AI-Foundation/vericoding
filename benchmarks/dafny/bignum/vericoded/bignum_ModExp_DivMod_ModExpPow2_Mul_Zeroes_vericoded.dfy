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
predicate AllZero(s: string)
{
  forall i | 0 <= i < |s| :: s[i] == '0'
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

method ModExpPow2(sx: string, sy: string, n: nat, sz: string) returns (res: string)
  requires ValidBitString(sx) && ValidBitString(sy) &&  ValidBitString(sz)
  // sy is power of 2 or zero
  requires Str2Int(sy) == Exp_int(2,n) || Str2Int(sy) == 0
  requires |sy| == n+1
  requires Str2Int(sz) > 1
  ensures ValidBitString(res)
  ensures Str2Int(res) == Exp_int(Str2Int(sx), Str2Int(sy)) % Str2Int(sz)
  decreases n
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

method Zeros(n: nat) returns (s: string)
  ensures |s| == n
  ensures ValidBitString(s)
  ensures Str2Int(s) == 0
  ensures AllZero(s)
{
  assume{:axiom} false;
}

// <vc-helpers>
method BitsToNat(s: string) returns (n: nat)
  requires ValidBitString(s)
  ensures n == Str2Int(s)
  decreases |s|
{
  if |s| == 0 {
    n := 0;
  } else {
    var prefix := s[0..|s|-1];
    var last := if s[|s|-1] == '1' then 1 else 0;
    var np := BitsToNat(prefix);
    n := 2 * np + last;
  }
}

method NatToBits(n: nat) returns (s: string)
  ensures ValidBitString(s) && Str2Int(s) == n && |s| > 0
  decreases n
{
  if n == 0 {
    s := "0";
  } else {
    var q := n / 2;
    var r := n % 2;
    var sq := NatToBits(q);
    if r == 1 {
      s := sq + "1";
    } else {
      s := sq + "0";
    }
  }
}

lemma ModMulZero(k: nat, z: nat)
  requires z > 0
  ensures (k * z) % z == 0
{
  // k*z < (k+1)*z because z > 0
  assert k * z < (k + 1) * z;
  // hence (k*z)/z == k
  assert (k * z) / z == k;
  // from division-remainder identity
  assert k * z == ((k * z) / z) * z + (k * z) % z;
  assert k * z == k * z + (k * z) % z;
  assert (k * z) % z == 0;
}

lemma DivBounds(t: nat, z: nat, s: nat)
  requires z > 0
  requires s * z <= t
  requires t < (s + 1) * z
  ensures t / z == s
{
  var u := t / z;
  assert u * z <= t;
  assert t < (u + 1) * z;
  if u < s {
    // then u + 1 <= s, so (u+1)*z <= s*z <= t contradicting t < (u+1)*z
    assert u + 1 <= s;
    assert (u + 1) * z <= s * z;
    assert s * z <= t;
    assert (u + 1) * z <= t;
    assert false;
  }
  if u > s {
    // then s + 1 <= u, so (s+1)*z <= u*z <= t contradicting t < (s+1)*z
    assert s + 1 <= u;
    assert (s + 1) * z <= u * z;
    assert u * z <= t;
    assert (s + 1) * z <= t;
    assert false;
  }
  // otherwise u == s
}

lemma AddMulZMod(a: nat, m: nat, z: nat)
  requires z > 0
  ensures (a + m*z) % z == a % z
{
  var q := a / z;
  var r := a % z;
  var s := q + m;
  // r < z because r is a % z and z > 0
  assert r < z;
  // bounds to determine division result
  assert s * z <= s * z + r;
  assert s * z + r < (s + 1) * z;
  DivBounds(s * z + r, z, s);
  assert (s * z + r) / z == s;
  assert (s * z + r) % z == r;
  assert a + m * z == s * z + r;
  assert (a + m * z) % z == r;
  assert a % z == r;
}

lemma MulMod(a: nat, b: nat, z: nat)
  requires z > 0
  ensures (a * b) % z == ((a % z) * b) % z
{
  var q := a / z;
  var r := a % z;
  assert a == q * z + r;
  var u := a * b;
  var v := r * b;
  var m := q * b;
  assert u == v + m * z;
  AddMulZMod(v, m, z);
  assert u % z == v % z;
  assert v % z == ((a % z) * b) % z;
}

method PowMod(x: nat, y: nat, z: nat) returns (r: nat)
  requires z > 0
  ensures r == Exp_int(x, y) % z
  decreases y
{
  r := 1 % z;
  var i := 0;
  while i < y
    invariant 0 <= i <= y
    invariant r == Exp_int(x, i) % z
    decreases y - i
  {
    var oldi := i;
    var oldr := r;
    var e := Exp_int(x, oldi);
    assert oldr == e % z;
    var newr := (oldr * x) % z;
    MulMod(e, x, z);
    assert newr == ((e * x) % z);
    // e * x == Exp_int(x, oldi + 1)
    assert (e * x) == Exp_int(x, oldi + 1);
    r := newr;
    i := oldi + 1;
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
  var x := BitsToNat(sx);
  var y := BitsToNat(sy);
  var z := BitsToNat(sz);
  var r := PowMod(x, y, z);
  res := NatToBits(r);
}
// </vc-code>

