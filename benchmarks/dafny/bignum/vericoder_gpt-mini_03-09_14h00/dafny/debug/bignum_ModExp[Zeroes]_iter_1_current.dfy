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

method Zeros(n: nat) returns (s: string)
  ensures |s| == n
  ensures ValidBitString(s)
  ensures Str2Int(s) == 0
  ensures AllZero(s)
{
  assume{:axiom} false;
}

// <vc-helpers>
ghost function Int2Bits(n: nat): string
  ensures ValidBitString(Int2Bits(n))
  ensures Str2Int(Int2Bits(n)) == n
  decreases n
{
  if n == 0 then "" else Int2Bits(n / 2) + (if n % 2 == 1 then "1" else "0")
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
    var m := Str2Int(sz);
    if sy[0] == '1' {
      return Int2Bits(Str2Int(sx) % m);
    } else {
      return Int2Bits(1 % m);
    }
  } else {
    var m := Str2Int(sz);
    var sxmod := Str2Int(sx) % m;
    var sy0 := sy[0..|sy|-1];
    var bit := sy[|sy|-1];
    var half := ModExp(sx, sy0, sz);
    var halfv := Str2Int(half);
    var t := (halfv * halfv) % m;
    var res_int := if bit == '1' then (t * sxmod) % m else t;
    return Int2Bits(res_int);
  }
}
// </vc-code>

