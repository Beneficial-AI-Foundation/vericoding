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

// <vc-helpers>
function Int2Str(n: nat): string
  decreases n
{
  if n == 0 then "0" else
    if n % 2 == 0 then Int2Str(n / 2) + "0" else Int2Str(n / 2) + "1"
}

lemma Int2Str_Str2Int_inverse(s: string)
  requires ValidBitString(s)
  ensures Int2Str(Str2Int(s)) == s
  decreases s
{
  if |s| == 0 then
    assert Str2Int(s) == 0;
    assert Int2Str(Str2Int(s)) == "0";
    assert s == "";
  else {
    var s' := s[0..|s|-1];
    var lastBit := if s[|s|-1] == '1' then 1 else 0;
    calc {
      Int2Str(Str2Int(s));
      Int2Str(2 * Str2Int(s') + lastBit);
      { assert lastBit < 2; }
      Int2Str((Str2Int(s') * 2 + lastBit) / 2) + (if (Str2Int(s') * 2 + lastBit) % 2 == 0 then "0" else "1");
      Int2Str(Str2Int(s') + lastBit / 2) + (if lastBit == 0 then "0" else "1");
      Int2Str(Str2Int(s')) + s[|s|-1..|s|];
      { Int2Str_Str2Int_inverse(s'); }
      s' + s[|s|-1..|s|];
      s;
    }
  }
}

lemma Add_lemma(s1: string, s2: string)
  requires ValidBitString(s1) && ValidBitString(s2)
  ensures exists res: string :: ValidBitString(res) && Str2Int(res) == Str2Int(s1) + Str2Int(s2)
{
  var n1 := Str2Int(s1);
  var n2 := Str2Int(s2);
  var sum := n1 + n2;
  var res := Int2Str(sum);
  assert ValidBitString(res);
  assert Str2Int(res) == sum;
}

lemma DivMod_lemma(dividend: string, divisor: string)
  requires ValidBitString(dividend) && ValidBitString(divisor)
  requires Str2Int(divisor) > 0
  ensures exists q: string, r: string ::
    ValidBitString(q) && ValidBitString(r) &&
    Str2Int(q) == Str2Int(dividend) / Str2Int(divisor) &&
    Str2Int(r) == Str2Int(dividend) % Str2Int(divisor)
{
  var n_dividend := Str2Int(dividend);
  var n_divisor := Str2Int(divisor);
  var q := n_dividend / n_divisor;
  var r := n_dividend % n_divisor;
  var s_q := Int2Str(q);
  var s_r := Int2Str(r);
  assert ValidBitString(s_q);
  assert ValidBitString(s_r);
  assert Str2Int(s_q) == q;
  assert Str2Int(s_r) == r;
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
  var base := Str2Int(sx);
  var exp := Str2Int(sy);
  var modulus := Str2Int(sz);
  
  if exp == 0 {
    res := Int2Str(1 % modulus);
  } else if exp == 1 {
    res := Int2Str(base % modulus);
  } else {
    var halfExp := exp / 2;
    var sy_half := Int2Str(halfExp);
    var halfRes := ModExp(sx, sy_half, sz);
    var halfResInt := Str2Int(halfRes);
    var square := (halfResInt * halfResInt) % modulus;
    if exp % 2 == 0 {
      res := Int2Str(square);
    } else {
      res := Int2Str((square * base) % modulus);
    }
  }
}
// </vc-code>

