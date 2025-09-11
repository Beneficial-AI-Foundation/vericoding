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

// <vc-helpers>
ghost function BinToNat(s: string): nat
  decreases s
  ensures BinToNat(s) == Str2Int(s)
{
  if |s| == 0 then 0 else 2 * BinToNat(s[0..|s|-1]) + (if s[|s|-1] == '1' then 1 else 0)
}

ghost function PowMod(a: nat, b: nat, m: nat): nat
  decreases b
  ensures if m == 0 then PowMod(a,b,m) == 0 else PowMod(a,b,m) == Exp_int(a,b) % m
{
  if m == 0 then 0
  else if b == 0 then 1 % m
  else if b % 2 == 1 then (a % m) * PowMod(a, b - 1, m) % m
  else
    var t := PowMod(a, b / 2, m);
    t * t % m
}

ghost function NatToBin(n: nat): string
  decreases n
  ensures Str2Int(NatToBin(n)) == n
  ensures ValidBitString(NatToBin(n))
{
  if n == 0 then ""
  else
    var q := n / 2;
    var r := n % 2;
    var prefix := if q == 0 then "" else NatToBin(q);
    prefix + (if r == 1 then "1" else "0")
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
  var a := BinToNat(sx);
  var b := BinToNat(sy);
  var m := BinToNat(sz);

  // Relate conversions to Str2Int so the postcondition can be proven
  assert a == Str2Int(sx);
  assert b == Str2Int(sy);
  assert m == Str2Int(sz);

  // From requires Str2Int(sz) > 1 we know m != 0
  assert m != 0;

  var r := PowMod(a, b, m);

  // PowMod's postcondition gives the modular exponentiation equality when m != 0
  assert r == PowMod(a, b, m);
  assert PowMod(a, b, m) == Exp_int(a, b) % m;

  res := NatToBin(r);

  // NatToBin's postcondition
  assert Str2Int(res) == r;

  // Chain equalities to establish the method's ensures
  assert Str2Int(res) == Exp_int(Str2Int(sx), Str2Int(sy)) % Str2Int(sz);
}
// </vc-code>

