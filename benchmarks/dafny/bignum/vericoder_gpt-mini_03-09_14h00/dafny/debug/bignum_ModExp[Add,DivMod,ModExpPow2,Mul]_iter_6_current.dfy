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

// <vc-helpers>
function BitsToNat(s: string): nat
  decreases s
{
  if |s| == 0 then 0 else 2 * BitsToNat(s[0..|s|-1]) + (if s[|s|-1] == '1' then 1 else 0)
}

function NatToBin(n: nat): string
  ensures ValidBitString(NatToBin(n))
  ensures Str2Int(NatToBin(n)) == n
  decreases n
{
  if n == 0 then "" else NatToBin(n / 2) + (if n % 2 == 1 then "1" else "0")
}

lemma BitsToNat_eq_Str2Int(s: string)
  requires ValidBitString(s)
  ensures Str2Int(s) == BitsToNat(s)
  decreases s
{
  if |s| == 0 {
    // both 0
  } else {
    BitsToNat_eq_Str2Int(s[0..|s|-1]);
    // by definitions
  }
}

lemma BitsToNat_prefix_cons(s: string, i: nat)
  requires ValidBitString(s)
  requires i < |s|
  ensures BitsToNat(s[0..i+1]) == 2 * BitsToNat(s[0..i]) + (if s[i] == '1' then 1 else 0)
{
  var prefix := s[0..i+1];
  // prefix non-empty
  assert |prefix| == i+1;
  assert prefix[|prefix|-1] == s[i];
  assert prefix[0..|prefix|-1] == s[0..i];
  // Unfold definition on prefix
  assert BitsToNat(prefix) == 2 * BitsToNat(prefix[0..|prefix|-1]) + (if prefix[|prefix|-1] == '1' then 1 else 0);
  assert BitsToNat(prefix[0..|prefix|-1]) == BitsToNat(s[0..i]);
  assert (if prefix[|prefix|-1] == '1' then 1 else 0) == (if s[i] == '1' then 1 else 0);
  assert BitsToNat(s[0..i+1]) == 2 * BitsToNat(s[0..i]) + (if s[i] == '1' then 1 else 0);
}

lemma Exp_one(x: nat)
  ensures Exp_int(x, 1) == x
{
  // Exp_int(x,1) == x * Exp_int(x,0) == x * 1 == x
}

lemma Exp_add(x: nat, y: nat, z: nat)
  ensures Exp_int(x, y + z) == Exp_int(x, y) * Exp_int(x, z)
  decreases z
{
  if z == 0 {
    // Exp_int(x,y+0) == Exp_int(x,y) and Exp_int(x,0) == 1
  } else {
    Exp_add(x, y, z - 1);
    // Inductive step
  }
}

lemma MulMod(x: nat, y: nat, m: nat)
  requires m > 0
  ensures (x % m) * (y % m) % m == (x * y) % m
{
  var rx := x % m;
  var qx := x / m;
  var ry := y % m;
  var qy := y / m;
  assert x == qx * m + rx;
  assert y == qy * m + ry;
  var prod := x * y;
  // Expand product
  assert prod == (qx * m + rx) * (qy * m + ry);
  assert prod == qx*qy*m*m + qx*m*ry + qy*m*rx + rx*ry;
  // Modulo m, all terms with factor m vanish
  assert prod % m == (rx * ry) % m;
  assert rx == x % m;
  assert ry == y % m;
  // Conclude (x% m)*(y% m) % m == (x*y)%m
  assert (x % m) * (y % m) % m == (rx * ry) % m;
  assert (rx * ry) % m == prod % m;
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
  // parse sx -> a
  var i := 0;
  var a := 0;
  while i < |sx|
    invariant 0 <= i <= |sx|
    invariant a == BitsToNat(sx[0..i])
    decreases |sx| - i
  {
    var bit := if sx[i] == '1' then 1 else 0;
    a := 2 * a + bit;
    i := i + 1;
  }

  // parse sy -> b
  i := 0;
  var b := 0;
  while i < |sy|
    invariant 0 <= i <= |sy|
    invariant b == BitsToNat(sy[0..i])
    decreases |sy| - i
  {
    var bit := if sy[i] == '1' then 1 else 0;
    // use lemma for prefix
    BitsToNat_prefix_cons(sy, i);
    b := 2 * b + bit;
    i := i + 1;
  }

  // parse sz -> m
  i := 0;
  var m := 0;
  while i < |sz|
    invariant 0 <= i <= |sz|
    invariant m == BitsToNat(sz[0..i])
    decreases |sz| - i
  {
    var bit := if sz[i] == '1' then 1 else 0;
    BitsToNat_prefix_cons(sz, i);
    m := 2 * m + bit;
    i := i + 1;
  }

  // Link BitsToNat to Str2Int so we can use preconditions (m > 1)
  BitsToNat_eq_Str2Int(sx);
  BitsToNat_eq_Str2Int(sy);
  BitsToNat_eq_Str2Int(sz);

  // m corresponds to full BitsToNat(sz)
  assert m == BitsToNat(sz);
  assert m == Str2Int(sz);
  assert m > 1;
  assert m > 0;

  // Use fast exponentiation processing bits of exponent from MSB to LSB (left-to-right)
  var resn := 1;
  var i2 := 0;
  while i2 < |sy|
    invariant 0 <= i2 <= |sy|
    invariant resn == Exp_int(a, BitsToNat(sy[0..i2])) % m
    decreases |sy| - i2
  {
    var bit := if sy[i2] == '1' then 1 else 0;
    // store old exponent value for invoking lemmas
    ghost var oldExp := BitsToNat(sy[0..i2]);

    // square: resn := resn * resn  => corresponds to exponent doubling
    // We maintain resn reduced modulo m at all times.
    ghost var E := Exp_int(a, oldExp);
    // ensure relation resn == E % m holds (from invariant)
    assert resn == E % m;

    // compute square modulo m
    resn := (resn * resn) % m;
    // use MulMod to relate (E% m * E% m)%m == (E*E)%m
    MulMod(E, E, m);
    assert resn == (E * E) % m;
    // justify exponent doubling: Exp_int(a, 2*oldExp) == Exp_int(a, oldExp) * Exp_int(a, oldExp)
    Exp_add(a, oldExp, oldExp);
    assert resn == Exp_int(a, 2 * oldExp) % m;

    if bit == 1 {
      // multiply by a to account for +1 in exponent
      ghost var F := Exp_int(a, 2 * oldExp);
      assert resn == F % m;
      resn := (resn * (a % m)) % m;
      // use MulMod to relate (F% m * a% m)%m == (F * a)%m
      MulMod(F, a, m);
      assert resn == (F * a) % m;
      // justify addition of 1 to exponent
      Exp_add(a, 2 * oldExp, 1);
      assert resn == Exp_int(a, 2 * oldExp + 1) % m;
    }

    i2 := i2 + 1;
  }

  // final result is resn mod m
  res := NatToBin(resn % m);
}
// </vc-code>

