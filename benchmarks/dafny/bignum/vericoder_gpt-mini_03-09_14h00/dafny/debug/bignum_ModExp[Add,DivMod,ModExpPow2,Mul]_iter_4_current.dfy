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

lemma Exp_add(x: nat, y: nat, z: nat)
  ensures Exp_int(x, y + z) == Exp_int(x, y) * Exp_int(x, z)
  decreases z
{
  if z == 0 {
    // Exp_int(x,y+0) == Exp_int(x,y) and Exp_int(x,0) == 1
  } else {
    Exp_add(x, y, z - 1);
    // Exp_int(x, y + z) == x * Exp_int(x, y + z - 1)
    // and by induction Exp_int(x, y + z - 1) == Exp_int(x, y) * Exp_int(x, z - 1)
    // so Exp_int(x, y + z) == x * (Exp_int(x, y) * Exp_int(x, z - 1))
    // == Exp_int(x, y) * (x * Exp_int(x, z - 1)) == Exp_int(x, y) * Exp_int(x, z)
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
    m := 2 * m + bit;
    i := i + 1;
  }

  // Use fast exponentiation by processing bits of exponent from LSB to MSB
  var resn := 1;
  var power := a % m;
  var k := 0;
  // invariant: resn % m == Exp_int(a, BitsToNat(sy[|sy|-k..|sy|])) % m
  // and power % m == Exp_int(a, Exp_int(2, k)) % m
  while k < |sy|
    invariant 0 <= k <= |sy|
    invariant resn % m == Exp_int(a, BitsToNat(sy[|sy|-k..|sy|])) % m
    invariant power % m == Exp_int(a, Exp_int(2, k)) % m
    decreases |sy| - k
  {
    var bit := if sy[|sy|-1-k] == '1' then 1 else 0;
    if bit == 1 {
      resn := (resn * power) % m;
    }
    // update power to a^{2^{k+1}} mod m
    power := (power * power) % m;
    k := k + 1;
  }

  // link BitsToNat to Str2Int for final equality
  BitsToNat_eq_Str2Int(sx);
  BitsToNat_eq_Str2Int(sy);
  BitsToNat_eq_Str2Int(sz);

  // after processing all bits, result equals a^b mod m
  // resn already is in 0..m-1; produce binary string
  res := NatToBin(resn % m);
}
// </vc-code>

