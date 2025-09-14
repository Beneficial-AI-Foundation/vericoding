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

// <vc-helpers>
ghost function Int2Str(n: nat): string
  decreases n
{
  if n == 0 then "0" else
    var r := n % 2;
    var s := Int2Str(n / 2);
    if r == 0 then s + "0" else s + "1"
}

ghost function RemoveLeadingZeros(s: string): string
  requires ValidBitString(s)
  ensures ValidBitString(RemoveLeadingZeros(s))
  ensures Str2Int(RemoveLeadingZeros(s)) == Str2Int(s)
  decreases |s|
{
  if |s| == 0 then "" else
    if s[0] == '0' then RemoveLeadingZeros(s[1..]) else s
}

method Mult(s1: string, s2: string) returns (res: string)
  requires ValidBitString(s1) && ValidBitString(s2)
  ensures ValidBitString(res)
  ensures Str2Int(res) == Str2Int(s1) * Str2Int(s2)
{
  var n1 := Str2Int(s1);
  var n2 := Str2Int(s2);
  res := Int2Str(n1 * n2);
}

method Mod(s1: string, s2: string) returns (res: string)
  requires ValidBitString(s1) && ValidBitString(s2)
  requires Str2Int(s2) > 0
  ensures ValidBitString(res)
  ensures Str2Int(res) == Str2Int(s1) % Str2Int(s2)
{
  var n1 := Str2Int(s1);
  var n2 := Str2Int(s2);
  res := Int2Str(n1 % n2);
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
      res := "1";
    } else {
      res := Mod(sx, sz);
    }
  } else {
    var rest := sy[0..|sy|-1];
    var last := sy[|sy|-1];
    var t := ModExp(sx, rest, sz);
    var t2 := Mult(t, t);
    if last == '0' {
      res := Mod(t2, sz);
    } else {
      var temp := Mult(t2, sx);
      res := Mod(temp, sz);
    }
  }
  res := RemoveLeadingZeros(res);
}
// </vc-code>

