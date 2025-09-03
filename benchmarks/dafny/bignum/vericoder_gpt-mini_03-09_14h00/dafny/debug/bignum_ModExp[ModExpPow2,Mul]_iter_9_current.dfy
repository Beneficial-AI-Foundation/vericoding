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
function method BinToNat(s: string): nat
  requires ValidBitString(s)
  decreases s
{
  var r := 0;
  var i := 0;
  while i < |s|
    decreases |s| - i
  {
    r := 2 * r + (if s[i] == '1' then 1 else 0);
    i := i + 1;
  }
  r
}

function method PowMod(x: nat, y: nat, m: nat): nat
  requires m > 0
  decreases y
{
  var res := 1;
  var b := x % m;
  var e := y;
  while e > 0
    decreases e
  {
    if e % 2 == 1 {
      res := (res * b) % m;
    }
    b := (b * b) % m;
    e := e / 2;
  }
  res
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
  var x := BinToNat(sx);
  var y := BinToNat(sy);
  var z := BinToNat(sz);
  var p := PowMod(x, y, z);
  res := Nat2Bin(p);
  Nat2Bin_ok(p);
  ghost {
    assert Str2Int(res) == p;
    assert x == Str2Int(sx);
    assert y == Str2Int(sy);
    assert z == Str2Int(sz);
    assert p == Exp_int(x, y) % z;
    assert Str2Int(res) == Exp_int(Str2Int(sx), Str2Int(sy)) % Str2Int(sz);
  }
}
// </vc-code>

