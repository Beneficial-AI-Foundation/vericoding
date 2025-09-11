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

method Mul(s1: string, s2: string) returns (res: string)
  requires ValidBitString(s1) && ValidBitString(s2)
  ensures ValidBitString(res)
  ensures Str2Int(res) == Str2Int(s1) * Str2Int(s2)
{
  assume{:axiom} false;
}

// <vc-helpers>
lemma ExpIntProperties(x: nat, y: nat)
  ensures y == 0 ==> Exp_int(x, y) == 1
  ensures y > 0 && y % 2 == 0 ==> Exp_int(x, y) == Exp_int(x * x, y / 2)
  ensures y > 0 && y % 2 == 1 ==> Exp_int(x, y) == x * Exp_int(x * x, y / 2)
{
  if y == 0 {
    // Base case: Exp_int(x, 0) == 1
  } else if y % 2 == 0 {
    // Even case: x^y = (x^2)^(y/2)
    calc {
      Exp_int(x, y);
      == x * Exp_int(x, y - 1);
      == x * x * Exp_int(x, y - 2);
      == Exp_int(x * x, y / 2);
    }
  } else {
    // Odd case: x^y = x * (x^2)^((y-1)/2)
    calc {
      Exp_int(x, y);
      == x * Exp_int(x, y - 1);
      == x * Exp_int(x * x, (y - 1) / 2);
      == x * Exp_int(x * x, y / 2);
    }
  }
}

lemma ModExpProperty(x: nat, y: nat, z: nat)
  requires z > 1
  requires y > 0
  ensures y % 2 == 0 ==> Exp_int(x, y) % z == Exp_int(x % z, y) % z
  ensures y % 2 == 1 ==> Exp_int(x, y) % z == ((x % z) * Exp_int(x % z, y - 1)) % z
{
  // This lemma helps establish the modular arithmetic properties
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
  if sy == "0" {
    res := "1";
    assert Str2Int("1") == 1;
    assert Exp_int(Str2Int(sx), 0) == 1;
    assert 1 % Str2Int(sz) < Str2Int(sz);
  } else if sy == "1" {
    var dummy: string;
    dummy, res := DivMod(sx, sz);
    assert Str2Int(sy) == 1;
    assert Exp_int(Str2Int(sx), 1) == Str2Int(sx);
    assert Str2Int(res) == Str2Int(sx) % Str2Int(sz);
  } else {
    // For sy > 1, use recursive approach
    // First divide sy by 2
    var sy_half: string;
    var sy_rem: string;
    sy_half, sy_rem := DivMod(sy, "10"); // Divide by 2 in binary
    
    // Recursive call with sy/2
    var temp := ModExp(sx, sy_half, sz);
    
    // Square the result
    var squared := Mul(temp, temp);
    var dummy: string;
    dummy, squared := DivMod(squared, sz);
    
    if sy_rem == "0" {
      // If sy was even, result is (x^(y/2))^2 mod z
      res := squared;
    } else {
      // If sy was odd, result is x * (x^(y/2))^2 mod z
      var product := Mul(squared, sx);
      dummy, res := DivMod(product, sz);
    }
    
    ExpIntProperties(Str2Int(sx), Str2Int(sy));
  }
}
// </vc-code>

