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

method DivMod(dividend: string, divisor: string) returns (quotient: string, remainder: string)
  requires ValidBitString(dividend) && ValidBitString(divisor)
  requires Str2Int(divisor) > 0
  ensures ValidBitString(quotient) && ValidBitString(remainder)
  ensures Str2Int(quotient) == Str2Int(dividend) / Str2Int(divisor)
  ensures Str2Int(remainder) == Str2Int(dividend) % Str2Int(divisor)
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

method Zeros(n: nat) returns (s: string)
  ensures |s| == n
  ensures ValidBitString(s)
  ensures Str2Int(s) == 0
  ensures AllZero(s)
{
  assume{:axiom} false;
}

// <vc-helpers>
lemma Lemma_ModExpBaseCase(x: nat, y: nat, z: nat)
  requires z > 1
  ensures Exp_int(x, y) % z == (if y == 0 then 1 % z else x * (Exp_int(x, y-1) % z) % z)
{
  if y > 0 {
    calc {
      Exp_int(x, y) % z;
      (x * Exp_int(x, y-1)) % z;
      (x * (Exp_int(x, y-1) % z)) % z;
    }
  }
}

lemma Lemma_PowerOfTwoDecomposition(s: string)
  requires ValidBitString(s)
  requires |s| > 0
  ensures Str2Int(s) == 2 * Str2Int(s[0..|s|-1]) + (if s[|s|-1] == '1' then 1 else 0)
{
}

lemma Lemma_ModExpRecursive(x: nat, y: nat, z: nat)
  requires z > 1
  ensures Exp_int(x, y) % z == 
    if y == 0 then 1 % z 
    else if y % 2 == 0 then (Exp_int(x, y/2) % z) * (Exp_int(x, y/2) % z) % z
    else x * (Exp_int(x, y-1) % z) % z
{
  if y > 0 {
    if y % 2 == 0 {
      calc {
        Exp_int(x, y) % z;
        Exp_int(x, y/2) * Exp_int(x, y/2) % z;
        (Exp_int(x, y/2) % z) * (Exp_int(x, y/2) % z) % z;
      }
    } else {
      calc {
        Exp_int(x, y) % z;
        x * Exp_int(x, y-1) % z;
        x * (Exp_int(x, y-1) % z) % z;
      }
    }
  }
}

lemma Lemma_LengthDecreases(s: string)
  requires |s| > 0
  ensures |s[0..|s|-1]| < |s|
{
}

lemma Lemma_ModIdentity(x: nat, z: nat)
  requires z > 1
  ensures x % z == x % z
{
}

lemma Lemma_OneModZ(z: nat)
  requires z > 1
  ensures 1 % z == 1
{
}

lemma Lemma_ModMultiplication(a: nat, b: nat, z: nat)
  requires z > 1
  ensures (a * b) % z == (a % z) * (b % z) % z
{
}

ghost function Int2Str(n: nat): string
  decreases n
{
  if n == 0 then "0" else
    if n == 1 then "1" else
      Int2Str(n / 2) + (if n % 2 == 0 then "0" else "1")
}

lemma Lemma_Int2StrValid(n: nat)
  ensures ValidBitString(Int2Str(n))
  decreases n
{
  if n > 1 {
    Lemma_Int2StrValid(n / 2);
  }
}

lemma Lemma_Int2StrCorrect(n: nat)
  ensures Str2Int(Int2Str(n)) == n
  decreases n
{
  if n > 1 {
    Lemma_Int2StrCorrect(n / 2);
    Lemma_PowerOfTwoDecomposition(Int2Str(n));
  }
}

lemma Lemma_ExpIntDiv2(x: nat, y: nat)
  requires y > 0
  ensures Exp_int(x, y/2) * Exp_int(x, y/2) == Exp_int(x, y) || Exp_int(x, y/2) * Exp_int(x, y/2) * x == Exp_int(x, y)
{
}

lemma Lemma_ModExpHelper(x: nat, y: nat, z: nat)
  requires z > 1
  ensures Exp_int(x, y) % z == 
    if y == 0 then 1 % z
    else if y == 1 then x % z
    else if y % 2 == 0 then (Exp_int(x, y/2) % z) * (Exp_int(x, y/2) % z) % z
    else x * (Exp_int(x, y-1) % z) % z
{
  if y == 0 {
  } else if y == 1 {
  } else if y % 2 == 0 {
    calc {
      Exp_int(x, y) % z;
      Exp_int(x, y/2) * Exp_int(x, y/2) % z;
      (Exp_int(x, y/2) % z) * (Exp_int(x, y/2) % z) % z;
    }
  } else {
    calc {
      Exp_int(x, y) % z;
      x * Exp_int(x, y-1) % z;
      x * (Exp_int(x, y-1) % z) % z;
    }
  }
}

lemma Lemma_Str2IntOneModZ(sz: string)
  requires ValidBitString(sz)
  requires Str2Int(sz) > 1
  ensures Str2Int("1") % Str2Int(sz) == 1
{
}

lemma Lemma_ModExpHelper2(x: nat, y: nat, z: nat)
  requires z > 1
  ensures Exp_int(x, y) % z == 
    if y == 0 then 1 % z
    else if y == 1 then x % z
    else if y % 2 == 0 then (Exp_int(x, y/2) % z) * (Exp_int(x, y/2) % z) % z
    else x * (Exp_int(x, y-1) % z) % z
{
}

ghost function ModExpGhost(sx: string, sy: string, sz: string): string
  requires ValidBitString(sx) && ValidBitString(sy) && ValidBitString(sz)
  requires Str2Int(sz) > 1
  ensures ValidBitString(result)
  ensures Str2Int(result) == Exp_int(Str2Int(sx), Str2Int(sy)) % Str2Int(sz)
  decreases |sy|
{
  var x_int := Str2Int(sx);
  var y_int := Str2Int(sy);
  var z_int := Str2Int(sz);
  
  if y_int == 0 {
    "1"
  } else if y_int == 1 {
    sx
  } else {
    var half_y := y_int / 2;
    var half_y_str := Int2Str(half_y);
    var temp := ModExpGhost(sx, half_y_str, sz);
    var temp_sq := Add(temp, temp);
    if y_int % 2 == 0 {
      temp_sq
    } else {
      Add(temp_sq, sx)
    }
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
  var x_int := Str2Int(sx);
  var y_int := Str2Int(sy);
  var z_int := Str2Int(sz);
  
  if y_int == 0 {
    res := "1";
  } else if y_int == 1 {
    res := sx;
  } else {
    var half_y := y_int / 2;
    var half_y_str := Int2Str(half_y);
    Lemma_Int2StrValid(half_y);
    Lemma_Int2StrCorrect(half_y);
    
    var temp := ModExp(sx, half_y_str, sz);
    var temp_int := Str2Int(temp);
    
    var temp_sq := Add(temp, temp);
    if y_int % 2 == 0 {
      res := temp_sq;
    } else {
      res := Add(temp_sq, sx);
    }
  }
}
// </vc-code>

