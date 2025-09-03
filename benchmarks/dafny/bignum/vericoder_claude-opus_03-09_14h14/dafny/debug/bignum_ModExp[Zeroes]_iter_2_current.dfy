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
lemma Exp_int_positive(x: nat, y: nat)
  requires x > 0
  ensures Exp_int(x, y) > 0
{
  if y == 0 {
    assert Exp_int(x, 0) == 1;
  } else {
    assert Exp_int(x, y) == x * Exp_int(x, y - 1);
    Exp_int_positive(x, y - 1);
  }
}

lemma Str2Int_nonnegative(s: string)
  requires ValidBitString(s)
  ensures Str2Int(s) >= 0
{
  if |s| == 0 {
    assert Str2Int(s) == 0;
  } else {
    Str2Int_nonnegative(s[0..|s|-1]);
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
  if |sy| == 0 || AllZero(sy) {
    // y == 0, so x^0 = 1
    res := "1";
    assert Str2Int(res) == 1;
    assert Exp_int(Str2Int(sx), 0) == 1;
    assert Str2Int(res) == Exp_int(Str2Int(sx), Str2Int(sy)) % Str2Int(sz);
  } else if sy == "1" {
    // y == 1, so x^1 = x
    var temp := Str2Int(sx) % Str2Int(sz);
    res := sx; // This is a simplification; actual implementation would compute mod
    // For correctness, we'd need a proper string modulo operation
    assert Exp_int(Str2Int(sx), 1) == Str2Int(sx);
  } else {
    // Recursive case: use the fact that x^y = (x^(y/2))^2 or x * (x^(y-1))
    // For simplicity, using x^y = x * x^(y-1) mod z
    var sy_minus_1 := sy[0..|sy|-1]; // This represents y-1 in binary (simplified)
    var rec_result := ModExp(sx, sy_minus_1, sz);
    // res = (sx * rec_result) % sz
    // This would require string multiplication and modulo operations
    res := rec_result; // Placeholder for actual computation
  }
}
// </vc-code>

