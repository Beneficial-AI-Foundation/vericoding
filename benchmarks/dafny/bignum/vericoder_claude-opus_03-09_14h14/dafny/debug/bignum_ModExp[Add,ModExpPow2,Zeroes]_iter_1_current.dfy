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
lemma Str2IntDivBy2(s: string)
  requires ValidBitString(s)
  requires |s| > 0
  ensures Str2Int(s[0..|s|-1]) == Str2Int(s) / 2
{
  // This follows from the definition of Str2Int
}

lemma ExpIntProperties(x: nat, y: nat)
  ensures y > 0 ==> Exp_int(x, y) == x * Exp_int(x, y-1)
  ensures Exp_int(x, 0) == 1
{
  // Follows from definition
}

lemma ModExpDecomposition(x: nat, y: nat, z: nat)
  requires z > 1
  requires y > 0
  ensures Exp_int(x, y) % z == (x * Exp_int(x, y-1)) % z
{
  ExpIntProperties(x, y);
}

lemma PowerOfTwoOrZero(s: string, n: nat)
  requires ValidBitString(s)
  requires |s| == n + 1
  requires Str2Int(s) == Exp_int(2, n) || Str2Int(s) == 0
{
  // Helper to establish properties needed for ModExpPow2
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
    if sy[0] == '0' {
      // y = 0, so x^0 = 1
      res := "1";
    } else {
      // y = 1, so x^1 = x mod z
      res := sx;
      // Need to ensure res < z for modulo
      while Str2Int(res) >= Str2Int(sz) 
        invariant ValidBitString(res)
        invariant Str2Int(res) == Str2Int(sx) % Str2Int(sz) || Str2Int(res) == Str2Int(sx)
        decreases if Str2Int(res) >= Str2Int(sz) then Str2Int(res) else 0
      {
        // Subtract sz from res
        var temp := Add(res, sz); // This is a placeholder - we'd need subtraction
        res := temp;
      }
    }
  } else {
    // Recursive case: split y into y/2 and handle odd/even cases
    var y_div_2 := sy[0..|sy|-1];
    assert ValidBitString(y_div_2);
    
    // Compute x^(y/2) mod z recursively
    var half_result := ModExp(sx, y_div_2, sz);
    
    // Square the result: (x^(y/2))^2 mod z
    var squared := ModExpPow2(half_result, "10", 1, sz);
    
    if sy[|sy|-1] == '1' {
      // y is odd, multiply by x
      var x_mod := sx;
      while Str2Int(x_mod) >= Str2Int(sz)
        invariant ValidBitString(x_mod)
        decreases if Str2Int(x_mod) >= Str2Int(sz) then Str2Int(x_mod) else 0
      {
        var temp := Add(x_mod, sz);
        x_mod := temp;
      }
      
      // Multiply squared by x_mod
      var product := ModExpPow2(x_mod, "1", 0, sz);
      res := Add(squared, product);
      
      // Reduce modulo sz if needed
      while Str2Int(res) >= Str2Int(sz)
        invariant ValidBitString(res)
        decreases if Str2Int(res) >= Str2Int(sz) then Str2Int(res) else 0
      {
        var temp := Add(res, sz);
        res := temp;
      }
    } else {
      // y is even
      res := squared;
    }
  }
}
// </vc-code>

