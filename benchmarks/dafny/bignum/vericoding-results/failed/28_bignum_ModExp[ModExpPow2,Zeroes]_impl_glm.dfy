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

method Zeros(n: nat) returns (s: string)
  ensures |s| == n
  ensures ValidBitString(s)
  ensures Str2Int(s) == 0
  ensures AllZero(s)
{
  assume{:axiom} false;
}

// <vc-helpers>
ghost function AppendBit(s: string, bit: bool): string
  requires ValidBitString(s)
  ensures ValidBitString(AppendBit(s, bit))
  ensures |AppendBit(s, bit)| == |s| + 1
  ensures Str2Int(AppendBit(s, bit)) == 2 * Str2Int(s) + (if bit then 1 else 0)
{
  s + (if bit then "1" else "0")
}

ghost function ModInt(x: nat, y: nat): nat
  requires y > 0
  ensures ModInt(x, y) < y
  ensures var q := x / y; var r := x % y; x == q * y + r && ModInt(x, y) == r
{
  x % y
}

function CreateZeros(n: nat): string
  ensures |CreateZeros(n)| == n
  ensures ValidBitString(CreateZeros(n))
  ensures Str2Int(CreateZeros(n)) == 0
  ensures AllZero(CreateZeros(n))
{
  if n == 0 then "" else CreateZeros(n - 1) + "0"
}

function NatToBitString(n: nat, len: nat): string
  requires len > 0
  ensures ValidBitString(NatToBitString(n, len))
  ensures |NatToBitString(n, len)| == len
  ensures Str2Int(NatToBitString(n, len)) == n % Exp_int(2, len)
  decreases len
{
  if len == 1 then
    if n % 2 == 1 then "1" else "0"
  else
    NatToBitString(n / 2, len - 1) + (if n % 2 == 1 then "1" else "0")
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
  if |sy| == 1 {
    if sy[0] == '0' {
      return CreateZeros(|sz|) + "1";
    } else {
      var x := Str2Int(sx);
      var z := Str2Int(sz);
      var res_int := x % z;
      return NatToBitString(res_int, |sz|);
    }
  } else {
    var n := |sy| - 1;
    var half_exp := ModExp(sx, sy[1..], sz);
    var half_squared := ModExp(half_exp, "10", sz);
    
    if sy[0] == '1' {
      var x_mod_z := ModExp(sx, "1", sz);
      var temp := ModExp(half_squared, x_mod_z, sz);
      return temp;
    } else {
      return half_squared;
    }
  }
}
// </vc-code>

