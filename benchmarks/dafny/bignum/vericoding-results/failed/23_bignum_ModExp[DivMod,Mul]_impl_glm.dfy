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

method Mul(s1: string, s2: string) returns (res: string)
  requires ValidBitString(s1) && ValidBitString(s2)
  ensures ValidBitString(res)
  ensures Str2Int(res) == Str2Int(s1) * Str2Int(s2)
{
  assume{:axiom} false;
}

// <vc-helpers>
function Str2Int(s: string): nat
  requires ValidBitString(s)
  decreases s
{
  if |s| == 0 then 0 else 2 * Str2Int(s[0..|s|-1]) + (if s[|s|-1] == '1' then 1 else 0)
}

function Exp_int(x: nat, y: nat): nat
{
  if y == 0 then 1 else x * Exp_int(x, y - 1)
}

function Int2Str(n: nat): string
{
  if n == 0 then "0" else Int2StrHelper(n, "")
}

function Int2StrHelper(n: nat, acc: string): string
  decreases n
{
  if n == 0 then acc else Int2StrHelper(n / 2, (if n % 2 == 1 then "1" else "0") + acc)
}

function Sub(s1: string, s2: string): string
  requires ValidBitString(s1) && ValidBitString(s2)
  requires Str2Int(s1) >= Str2Int(s2)
  ensures ValidBitString(Sub(s1, s2))
  ensures Str2Int(Sub(s1, s2)) == Str2Int(s1) - Str2Int(s2)
{
  Int2Str(Str2Int(s1) - Str2Int(s2))
}

function Add(s1: string, s2: string): string
  requires ValidBitString(s1) && ValidBitString(s2)
  ensures ValidBitString(Add(s1, s2))
  ensures Str2Int(Add(s1, s2)) == Str2Int(s1) + Str2Int(s2)
{
  Int2Str(Str2Int(s1) + Str2Int(s2))
}

function Mul(s1: string, s2: string): string
  requires ValidBitString(s1) && ValidBitString(s2)
  ensures ValidBitString(Mul(s1, s2))
  ensures Str2Int(Mul(s1, s2)) == Str2Int(s1) * Str2Int(s2)
{
  Int2Str(Str2Int(s1) * Str2Int(s2))
}

function Div(s1: string, s2: string): string
  requires ValidBitString(s1) && ValidBitString(s2)
  requires Str2Int(s2) > 0
  ensures ValidBitString(Div(s1, s2))
  ensures Str2Int(Div(s1, s2)) == Str2Int(s1) / Str2Int(s2)
{
  Int2Str(Str2Int(s1) / Str2Int(s2))
}

function Mod(s1: string, s2: string): string
  requires ValidBitString(s1) && ValidBitString(s2)
  requires Str2Int(s2) > 0
  ensures ValidBitString(Mod(s1, s2))
  ensures Str2Int(Mod(s1, s2)) == Str2Int(s1) % Str2Int(s2)
{
  Int2Str(Str2Int(s1) % Str2Int(s2))
}

function StrRightShift(s: string): string
  requires ValidBitString(s)
  ensures |s| > 0 ==> |StrRightShift(s)| == |s| - 1
  ensures |s| > 0 ==> ValidBitString(StrRightShift(s))
  ensures |s| > 0 ==> Str2Int(StrRightShift(s)) == Str2Int(s) / 2
{
  if |s| == 0 then "" else s[0..|s|-1]
}

function IsEven(s: string): bool
  requires ValidBitString(s)
  ensures |s| > 0 ==> IsEven(s) == (Str2Int(s) % 2 == 0)
{
  |s| == 0 || s[|s|-1] == '0'
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
  if |sy| == 1 && sy == "1" {
    return Mod(sx, sz);
  }
  
  var half := StrRightShift(sy);
  var temp := ModExp(sx, half, sz);
  var squared := Mul(temp, temp);
  
  if IsEven(sy) {
    return Mod(squared, sz);
  } else {
    var multiplied := Mul(squared, sx);
    return Mod(multiplied, sz);
  }
}
// </vc-code>

