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
lemma LemmaPowZero(x: nat)
  ensures Exp_int(x, 0) == 1
{
}

lemma LemmaPowOne(x: nat)
  ensures Exp_int(x, 1) == x
{
}

lemma LemmaPowTwo(x: nat)
  ensures Exp_int(x, 2) == x * x
{
}

lemma LemmaModPowZero(x: nat, m: nat)
  requires m > 1
  ensures Exp_int(x, 0) % m == 1
{
}

lemma LemmaModExpIdentity(a: nat, b: nat, m: nat)
  requires m > 1
  requires b > 0
  ensures Exp_int(a, b) % m == ((a % m) * (Exp_int(a, b - 1) % m)) % m
{
}

lemma LemmaPowOfPower2(x: nat, n: nat)
  requires n > 0
  ensures Exp_int(x, Exp_int(2, n)) == Exp_int(Exp_int(x, Exp_int(2, n - 1)), 2)
{
}

lemma LemmaModPowSquare(a: nat, m: nat)
  requires m > 1
  ensures (a * a) % m == (a % m) * (a % m) % m
{
}

function CreateZeroString(n: nat): string
  decreases n
{
  if n == 0 then "" else "0" + CreateZeroString(n - 1)
}

ghost function Add_int(s1: string, s2: string): nat
  requires ValidBitString(s1) && ValidBitString(s2)
  ensures Add_int(s1, s2) == Str2Int(s1) + Str2Int(s2)
{
  Str2Int(s1) + Str2Int(s2)
}

ghost function Str2IntOfZeroString(n: nat): nat
  ensures Str2IntOfZeroString(n) == 0
  decreases n
{
  if n == 0 then 0 else 2 * Str2IntOfZeroString(n - 1) + 0
}

lemma LemmaZeroStringLength(n: nat)
  ensures |CreateZeroString(n)| == n
{
}

lemma LemmaZeroStringValid(n: nat)
  ensures ValidBitString(CreateZeroString(n))
{
}

ghost function CreateZeroStringInt(n: nat): string
  ensures ValidBitString(CreateZeroStringInt(n))
  ensures |CreateZeroStringInt(n)| == n
  ensures Str2Int(CreateZeroStringInt(n)) == 0
  decreases n
{
  if n == 0 then 
    "" 
  else 
    "0" + CreateZeroStringInt(n - 1)
}

lemma LemmaStr2IntConcatZero(s: string, n: nat)
  requires ValidBitString(s)
  requires n >= 0
  ensures Str2Int(s + CreateZeroStringInt(n)) == Str2Int(s) * Exp_int(2, n)
{
}

lemma LemmaTwoToN(n: nat)
  ensures Exp_int(2, n) == 2 * Exp_int(2, n - 1) when n > 0
  ensures Exp_int(2, 0) == 1
{
}
// </vc-helpers>
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
  var ghost sy_val := Str2Int(sy);
  var ghost sz_val := Str2Int(sz);
  
  if (n == 0) {
    if (sy_val == 0) {
      res := "1";
    } else {
      var divmod_res_result, rem_result := DivMod(sx, sz);
      res := rem_result;
    }
  } else {
    var half_n := n - 1;
    var half_sy : string;
    ghost var zero_string := CreateZeroStringInt(half_n);
    half_sy := "0" + zero_string;
    
    var temp := ModExpPow2(sx, half_sy, half_n, sz);
    var mul_temp: string;
    mul_temp := Add(temp, temp);
    var divmod_res_result, rem_result := DivMod(mul_temp, sz);
    res := rem_result;
  }
}
// </vc-code>

