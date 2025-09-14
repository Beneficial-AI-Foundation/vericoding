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
function Str2Int(s: string): nat
  requires ValidBitString(s)
  decreases s
{
  if |s| == 0 then  0  else  (2 * Str2Int(s[0..|s|-1]) + (if s[|s|-1] == '1' then 1 else 0))
}
function Exp_int(x: nat, y:nat): nat
{
  if y == 0 then 1 else x * Exp_int(x, y - 1)
}
predicate ValidBitString(s: string)
{
  forall i | 0 <= i < |s| :: s[i] == '0' || s[i] == '1'
}
predicate AllZero(s: string)
{
  forall i | 0 <= i < |s| :: s[i] == '0'
}
function Char(n: nat): string
  requires n < 2
{
  if n == 0 then "0" else "1"
}
function Bitstring(n: nat): string
  ensures ValidBitString(Bitstring(n))
  ensures Str2Int(Bitstring(n)) == n
{
  if n == 0 then "0" else Bitstring(n / 2) + Char(n % 2)
}
function RemoveLast(s: string): string
  requires |s| > 0
  ensures ValidBitString(s) ==> ValidBitString(RemoveLast(s))
  ensures ValidBitString(s) ==> Str2Int(RemoveLast(s)) == Str2Int(s) / 2
{
  s[..|s|-1]
}
method Mod(s1: string, s2: string) returns (res: string)
  requires ValidBitString(s1) && ValidBitString(s2)
  requires Str2Int(s2) > 0
  ensures ValidBitString(res)
  ensures Str2Int(res) == Str2Int(s1) % Str2Int(s2)
{
  var a := Str2Int(s1);
  var b := Str2Int(s2);
  var mod := a % b;
  res := Bitstring(mod);
}
function Zeros(n: nat): string
  ensures |Zeros(n)| == n
  ensures ValidBitString(Zeros(n))
  ensures Str2Int(Zeros(n)) == 0
  ensures AllZero(Zeros(n))
{
  if n == 0 then "" else "0" + Zeros(n - 1)
}
method Mul(s1: string, s2: string) returns (res: string)
  requires ValidBitString(s1) && ValidBitString(s2)
  ensures ValidBitString(res)
  ensures Str2Int(res) == Str2Int(s1) * Str2Int(s2)
{
  var x := Str2Int(s1);
  var y := Str2Int(s2);
  var p := x * y;
  res := Bitstring(p);
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
    if Str2Int(sy) == 0 {
      res := Bitstring(1 % Str2Int(sz));
    } else { // sy == "1"
      var x_mod := Mod(sx, sz);
      res := x_mod;
    }
  } else {
    var sq := Mul(sx, sx);
    var sq_mod_str := Mod(sq, sz);
    var sub_sy := RemoveLast(sy);
    var res_sub := ModExp(sq_mod_str, sub_sy, sz);
    if sy[|sy|-1] == '1' {
      var temp := Mul(res_sub, sx);
      res := Mod(temp, sz);
    } else {
      res := res_sub;
    }
  }
}
// </vc-code>

