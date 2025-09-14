ghost function Exp_int(x: nat, y:nat): nat
{
  if y == 0 then 1 else x * Exp_int(x, y - 1)
}
predicate ValidBitString(s: string)
{
  // All characters must be '0' or '1'.
  forall i | 0 <= i < |s| :: s[i] == '0' || s[i] == '1'
}
ghost function Str2Int(s: string): nat
  requires ValidBitString(s)
  decreases s
{
  if |s| == 0 then  0  else  (2 * Str2Int(s[0..|s|-1]) + (if s[|s|-1] == '1' then 1 else 0))
}

method Add(s1: string, s2: string) returns (res: string)
  requires ValidBitString(s1) && ValidBitString(s2)
  ensures ValidBitString(res)
  ensures Str2Int(res) == Str2Int(s1) + Str2Int(s2)
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
function method AddWithCarry(s1: string, s2: string, carry: bool): (string, bool)
  requires ValidBitString(s1) && ValidBitString(s2)
  requires |s1| == |s2|
  decreases |s1|
  ensures ValidBitString(Var0)
  ensures if carry then Str2Int(Var0) + Exp_int(2, |s1|) == Str2Int(s1) + Str2Int(s2) + 1 
  else Str2Int(Var0) + 2 * (if Var1 then 1 else 0) == Str2Int(s1) + Str2Int(s2)
{
  if |s1| == 0 then ("", carry) else
    var c1 := s1[|s1|-1] == '1';
    var c2 := s2[|s2|-1] == '1';
    var sum := (if c1 then 1 else 0) + (if c2 then 1 else 0) + (if carry then 1 else 0);
    var new_carry := sum >= 2;
    var bit := sum % 2;
    var (ls, _) := AddWithCarry(s1[..|s1|-1], s2[..|s2|-1], new_carry);
    (ls + (if bit == 1 then "1" else "0"), new_carry)
}

lemma AddWithCarryCorrect(s1: string, s2: string, carry: bool)
  requires ValidBitString(s1) && ValidBitString(s2)
  requires |s1| == |s2|
  ensures var (s, c) := AddWithCarry(s1, s2, carry); ValidBitString(s)
  ensures var (s, c) := AddWithCarry(s1, s2, carry); 
      if carry then 
          Str2Int(s) + Exp_int(2, |s1|) == Str2Int(s1) + Str2Int(s2) + 1 
      else 
          Str2Int(s) + 2 * (if c then 1 else 0) == Str2Int(s1) + Str2Int(s2)
{
  if |s1| == 0 {
  } else {
    var c1 := s1[|s1|-1] == '1';
    var c2 := s2[|s2|-1] == '1';
    var sum := (if c1 then 1 else 0) + (if c2 then 1 else 0) + (if carry then 1 else 0);
    var new_carry := sum >= 2;
    var bit := sum % 2;
    
    AddWithCarryCorrect(s1[..|s1|-1], s2[..|s2|-1], new_carry);
    var (ls, lc) := AddWithCarry(s1[..|s1|-1], s2[..|s2|-1], new_carry);
    calc {
      Str2Int(s1) + Str2Int(s2) + (if carry then 1 else 0);
      (Exp_int(2, |s1|-1) * Str2Int(s1[..|s1|-1]) + (if c1 then 1 else 0)) +
      (Exp_int(2, |s1|-1) * Str2Int(s2[..|s2|-1]) + (if c2 then 1 else 0)) +
      (if carry then 1 else 0);
      Exp_int(2, |s1|-1) * (Str2Int(s1[..|s1|-1]) + Str2Int(s2[..|s2|-1])) + (sum);
      { 
        if new_carry {
          assert Str2Int(ls) + Exp_int(2, |s1|-1) == Str2Int(s1[..|s1|-1]) + Str2Int(s2[..|s2|-1]) + new_carry;
          assert Str2Int(ls) + Exp_int(2, |s1|-1) == Str2Int(s1[..|s1|-1]) + Str2Int(s2[..|s2|-1]) + 1;
        } else {
          assert Str2Int(ls) + 2 * (if lc then 1 else 0) == Str2Int(s1[..|s1|-1]) + Str2Int(s2[..|s2|-1]);
        }
      }
      Exp_int(2, |s1|-1) * Str2Int(ls) + 2 * Exp_int(2, |s1|-1) * (if new_carry then 1 else 0) + (sum);
      Exp_int(2, |s1|-1) * Str2Int(ls) + 2 * Exp_int(2, |s1|-1) * (sum / 2) + (sum % 2);
      Exp_int(2, |s1|-1) * Str2Int(ls) + sum;
      Exp_int(2, |s1|-1) * Str2Int(ls) + bit + 2 * (if new_carry then 1 else 0);
      Str2Int(ls + (if bit == 1 then "1" else "0")) + 2 * (if new_carry then 1 else 0);
    }
  }
}

function method LeftPad(s: string, k: nat): string
  requires ValidBitString(s)
  requires |s| <= k
  ensures ValidBitString(Var0)
  ensures |Var0| == k
  ensures Str2Int(Var0) == Str2Int(s)
{
  if |s| == k then s else "0" + LeftPad(s, k-1)
}

function method RightShift(s: string, k: nat): string
  requires ValidBitString(s)
  requires k >= 0
  requires k <= |s|
  ensures ValidBitString(Var0)
  ensures |Var0| == |s| - k
  ensures Str2Int(Var0) * Exp_int(2, k) == Str2Int(s)
{
  if k == 0 then s else if |s| == 0 then "" else RightShift(s[0..|s|-1], k-1)
}

function method LengthCheck(s1: string, s2: string): string
  requires ValidBitString(s1) && ValidBitString(s2)
  ensures ValidBitString(Var0)
  ensures |Var0| == |s1|
  ensures Str2Int(Var0) == Str2Int(s2)
{
  if |s1| <= |s2| then s2[|s2| - |s1| ..] else LeftPad(s2, |s1|)
}

method Add(s1: string, s2: string) returns (res: string)
  requires ValidBitString(s1) && ValidBitString(s2)
  ensures ValidBitString(res)
  ensures Str2Int(res) == Str2Int(s1) + Str2Int(s2)
{
    var max_len := if |s1| > |s2| then |s1| else |s2|;
    var s1_padded := LeftPad(s1, max_len + 1);
    var s2_padded := LeftPad(s2, max_len + 1);
    var (sum, _) := AddWithCarry(s1_padded, s2_padded, false);
    if sum == "" {
        res := "0";
    } else {
        res := sum;
    }
}

method Mul(s1: string, s2: string) returns (res: string)
  requires ValidBitString(s1) && ValidBitString(s2)
  ensures ValidBitString(res)
  ensures Str2Int(res) == Str2Int(s1) * Str2Int(s2)
{
    if Str2Int(s1) == 0 || Str2Int(s2) == 0 {
        res := "0";
        return;
    }
    var len1 := |s1|;
    var len2 := |s2|;
    var max_len := len1 + len2;
    res := LeftPad("0", max_len);

    for i := 0 to len1
        invariant ValidBitString(res)
        invariant Str2Int(res) == Str2Int(s1[..i]) * Str2Int(s2)
    {
        var bit := s1[i] == '1';
        if bit {
            var partial_product := LeftPad(s2, max_len);
            var shifted_partial := partial_product + LeftPad("", len1 - 1 - i);
            shifted_partial := LeftPad(shifted_partial, max_len);
            var temp := Add(res, shifted_partial);
            res := temp;
        }
    }
}

lemma MulCorrect(s1: string, s2: string)
    requires ValidBitString(s1) && ValidBitString(s2)
    ensures var r := Mul(s1, s2); ValidBitString(r) && Str2Int(r) == Str2Int(s1) * Str2Int(s2)
{
}
// </vc-helpers>

// <vc-spec>
method ModExpPow2(sx: string, sy: string, n: nat, sz: string) returns (res: string)
  requires ValidBitString(sx) && ValidBitString(sy) &&  ValidBitString(sz)
  // sy is power of 2 or zero
  requires Str2Int(sy) == Exp_int(2,n) || Str2Int(sy) == 0
  requires |sy| == n+1
  requires Str2Int(sz) > 1
  ensures ValidBitString(res)
  ensures Str2Int(res) == Exp_int(Str2Int(sx), Str2Int(sy)) % Str2Int(sz)
  decreases n
// </vc-spec>
// <vc-code>
if Str2Int(sy) == 0 {
    res := "1";
} else if Str2Int(sx) == 0 {
    res := "0";
} else if sx == "1" {
    res := "1";
} else if n == 0 {
    var (_, c) := AddWithCarry("1", sz, false);
    if c {
        res := "0";
    } else {
        res := "1";
    }
} else {
    var n_str := sy[..|sy|-1];
    var half_power := ModExpPow2(sx, n_str, n-1, sz);
    var temp := Mul(half_power, half_power);
    if |temp| < |sz| {
        temp := LeftPad(temp, |sz|);
    }
    var (_, carry) := AddWithCarry(temp, sz, false);
    if carry {
        var (sum, _) := AddWithCarry(temp, sz, false);
        res := sum[..|sum|-1];
    } else {
        res := temp;
    }
    if |res| < |sz| {
        res := LeftPad(res, |sz|);
    } else if |res| > |sz| {
        res := res[|res| - |sz| ..];
    }
}
// </vc-code>

