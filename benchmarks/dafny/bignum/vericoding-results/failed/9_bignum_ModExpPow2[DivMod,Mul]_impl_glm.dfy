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

method DivMod(dividend: string, divisor: string) returns (quotient: string, remainder: string)
  requires ValidBitString(dividend) && ValidBitString(divisor)
  requires Str2Int(divisor) > 0
  ensures ValidBitString(quotient) && ValidBitString(remainder)
  ensures Str2Int(quotient) == Str2Int(dividend) / Str2Int(divisor)
  ensures Str2Int(remainder) == Str2Int(dividend) % Str2Int(divisor)
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

method DivMod(dividend: string, divisor: string) returns (quotient: string, remainder: string)
  requires ValidBitString(dividend) && ValidBitString(divisor)
  requires Str2Int(divisor) > 0
  ensures ValidBitString(quotient) && ValidBitString(remainder)
  ensures Str2Int(quotient) == Str2Int(dividend) / Str2Int(divisor)
  ensures Str2Int(remainder) == Str2Int(dividend) % Str2Int(divisor)
{
  var x := Str2Int(dividend);
  var y := Str2Int(divisor);
  ghost {
    Int2StrCorrect(x / y);
    Int2StrCorrect(x % y);
  }
  quotient := Int2Str(x / y);
  remainder := Int2Str(x % y);
}

method Mul(s1: string, s2: string) returns (res: string)
  requires ValidBitString(s1) && ValidBitString(s2)
  ensures ValidBitString(res)
  ensures Str2Int(res) == Str2Int(s1) * Str2Int(s2)
{
  var x := Str2Int(s1);
  var y := Str2Int(s2);
  ghost {
    Int2StrCorrect(x * y);
  }
  res := Int2Str(x * y);
}

function Int2Str(x: nat): string
  decreases x
{
  if x == 0 then "0"
  else
    var s := Int2Str(x / 2);
    if s == "0" then
      if x % 2 == 1 then "1" else "0"
    else
      if x % 2 == 1 then s + "1" else s + "0"
}

lemma Int2StrCorrect(x: nat)
  ensures ValidBitString(Int2Str(x))
  ensures Str2Int(Int2Str(x)) == x
  decreases x
{
  if x != 0 {
    var s := Int2Str(x / 2);
    calc {
      Str2Int(Int2Str(x));
      Str2Int(if s == "0" then (if x % 2 == 1 then "1" else "0") else s + (if x % 2 == 1 then "1" else "0"));
      { if s == "0" {
          calc {
            Str2Int(if x % 2 == 1 then "1" else "0");
            (if x % 2 == 1 then 1 else 0);
            x % 2;
          }
        } else {
          calc {
            Str2Int(s + (if x % 2 == 1 then "1" else "0"));
            2 * Str2Int(s) + (if x % 2 == 1 then 1 else 0);
            { Int2StrCorrect(x / 2); }
            2 * (x / 2) + (x % 2);
            x;
          }
        }
      }
      x;
    }
  }
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
{
  if n == 0 {
    if sy == "0" {
      res := "1"; // sx^0 = 1
    } else {
      // Case sy != "0". Since |sy| == n+1, n==0 implies |sy| == 1.
      // The only other 1-bit string is "1".
      // The pre-condition states Str2Int(sy) == Exp_int(2,n) || Str2Int(sy) == 0.
      // Since sy != "0", it must be that Str2Int(sy) == Exp_int(2,0) == 1.
      // Therefore sy must be "1".
      assert sy == "1";
      // We need to compute sx^1 % sz, which is sx % sz.
      var _, rem := DivMod(sx, sz);
      res := rem;
    }
  } else {
    var n_decremented := n - 1;
    // sy represents 2^n, so it is a "1" followed by n "0"s.
    // sy[0..|sy|-1] takes the prefix of length |sy| - 1 = n.
    // This prefix is a "1" followed by n-1 "0"s, which represents 2^(n-1).
    var sy_prefix := sy[0..|sy|-1];
    
    // Recursive call: compute sx^(2^(n-1)) % sz
    var temp := ModExpPow2(sx, sy_prefix, n_decremented, sz);
    // temp is now equal to Exp_int(Str2Int(sx), Exp_int(2, n-1)) % Str2Int(sz)
    
    // We need to square temp and mod by sz.
    // temp * temp = (sx^(2^(n-1)) % sz)^2
    // We need to show (sx^(2^(n-1)) % sz)^2 % sz = sx^(2^n) % sz
    
    // By modular arithmetic property: (a % b)^2 % b = a^2 % b.
    // So, (temp * temp) % sz = (sx^(2^(n-1)))^2 % sz = sx^(2^n) % sz.
    
    var squared := Mul(temp, temp);
    var _, rem := DivMod(squared, sz);
    res := rem;
  }
}
// </vc-code>

