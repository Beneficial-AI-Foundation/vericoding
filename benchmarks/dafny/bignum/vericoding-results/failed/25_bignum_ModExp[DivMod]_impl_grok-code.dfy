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

method DivMod(dividend: string, divisor: string) returns (quotient: string, remainder: string)
  requires ValidBitString(dividend) && ValidBitString(divisor)
  requires Str2Int(divisor) > 0
  ensures ValidBitString(quotient) && ValidBitString(remainder)
  ensures Str2Int(quotient) == Str2Int(dividend) / Str2Int(divisor)
  ensures Str2Int(remainder) == Str2Int(dividend) % Str2Int(divisor)
{
  assume{:axiom} false;
}

// <vc-helpers>
function Int2Str(n: nat): (s: string)
  decreases n
  ensures ValidBitString(s)
{
  if n == 0 then "0" else Int2Str(n / 2) + if n % 2 == 1 then "1" else "0"
}

function AddStrings(a: string, b: string, carry: nat): (res: string)
  requires ValidBitString(a)
  requires ValidBitString(b)
  requires carry == 0 || carry == 1
  decreases |a| + |b|
  ensures ValidBitString(res)
  ensures Str2Int(res) <= Str2Int(a) + Str2Int(b) + carry
  ensures (|a| >= 1 || |b| >= 1 || carry == 0 || res == "1") &&
          ((|a| == 0 && |b| == 0 && carry == 0) ==> res == "") &&
          ((|a| == 0 && |b| == 0 && carry == 1) ==> res == "1")
{
  if |a| == 0 && |b| == 0 then
    if carry == 0 then "" else "1"
  else if |a| == 0 then
    if carry == 0 then b else AddStrings("", b, carry)
  else if |b| == 0 then
    if carry == 0 then a else AddStrings(a, "", carry)
  else
    var a_last := if a[|a|-1] == '1' then 1 else 0;
    var b_last := if b[|b|-1] == '1' then 1 else 0;
    var sum := a_last + b_last + carry;
    var bit := if sum % 2 == 1 then '1' else '0';
    var new_carry := if sum >= 2 then 1 else 0;
    var res_rest := AddStrings(a[..|a|-1], b[..|b|-1], new_carry);
    res_rest + [bit]
}

function MultiplyStrings(left: string, right: string): (res: string)
  requires ValidBitString(left) && ValidBitString(right)
  ensures ValidBitString(res)
  ensures Str2Int(res) == Str2Int(left) * Str2Int(right)
{
  if |right| == 0 then "0"
  else if |right| == 1 then
    if right[0] == '0' then "0" else left
  else
    var half := right[..|right|-1];
    var prod_half := MultiplyStrings(left, half);
    var shifted := prod_half + "0";
    if right[|right|-1] == '1' then
      AddStrings(shifted, left, 0)
    else
      shifted
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
  var quotient, remainder := DivMod(sx, sz);
  var base_str := remainder;
  var result_str := "1";
  var i := 0;
  while i < |sy|
    decreases |sy| - i
  {
    var sq := MultiplyStrings(result_str, result_str);
    var sq_quot, sq_rem := DivMod(sq, sz);
    if sy[i] == '1' {
      var prod := MultiplyStrings(sq_rem, base_str);
      var prod_quot, prod_rem := DivMod(prod, sz);
      result_str := prod_rem;
    } else {
      result_str := sq_rem;
    }
    i := i + 1;
  }
  res := result_str;
}
// </vc-code>

