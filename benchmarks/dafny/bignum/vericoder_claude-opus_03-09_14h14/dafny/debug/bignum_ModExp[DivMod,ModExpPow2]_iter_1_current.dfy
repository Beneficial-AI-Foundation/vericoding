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

// <vc-helpers>
lemma ExpIntProperties(x: nat, y: nat)
  ensures y > 0 ==> Exp_int(x, y) == x * Exp_int(x, y - 1)
  ensures Exp_int(x, 0) == 1
{
}

lemma ModExpProperty(x: nat, y: nat, z: nat)
  requires z > 0
  requires y > 0
  ensures (Exp_int(x, y) % z) == ((x % z) * (Exp_int(x, y - 1) % z)) % z
{
  calc == {
    Exp_int(x, y) % z;
    (x * Exp_int(x, y - 1)) % z;
    ((x % z) * (Exp_int(x, y - 1) % z)) % z;
  }
}

lemma Str2IntZeroString()
  ensures ValidBitString("0")
  ensures Str2Int("0") == 0
{
}

lemma Str2IntOneString()
  ensures ValidBitString("1")
  ensures Str2Int("1") == 1
{
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
  if Str2Int(sy) == 0 {
    Str2IntOneString();
    res := "1";
    return;
  }
  
  var y_minus_1_str: string;
  var dummy: string;
  
  // Compute y - 1
  Str2IntOneString();
  y_minus_1_str, dummy := DivMod(sy, "1");
  assert Str2Int(y_minus_1_str) == Str2Int(sy) - 1;
  
  // Recursive call for x^(y-1) mod z
  var temp := ModExp(sx, y_minus_1_str, sz);
  
  // Compute (x mod z)
  var x_mod_z: string;
  var dummy2: string;
  dummy2, x_mod_z := DivMod(sx, sz);
  
  // Multiply (x mod z) * (x^(y-1) mod z)
  var product := "";
  var i := 0;
  while i < Str2Int(x_mod_z)
    invariant 0 <= i <= Str2Int(x_mod_z)
    invariant ValidBitString(product)
    invariant Str2Int(product) == i * Str2Int(temp)
    decreases Str2Int(x_mod_z) - i
  {
    // Add temp to product
    var j := 0;
    var carry := "0";
    var new_product := "";
    
    while j < |product| || j < |temp| || Str2Int(carry) > 0
      invariant ValidBitString(new_product)
      invariant ValidBitString(carry)
      invariant Str2Int(carry) <= 1
      decreases if Str2Int(carry) > 0 then 1000000 - j else (|product| + |temp|) - j
    {
      var digit_sum := 0;
      
      if j < |product| {
        digit_sum := digit_sum + (if product[j] == '1' then 1 else 0);
      }
      if j < |temp| {
        digit_sum := digit_sum + (if temp[j] == '1' then 1 else 0);
      }
      digit_sum := digit_sum + Str2Int(carry);
      
      new_product := new_product + (if digit_sum % 2 == 1 then "1" else "0");
      carry := if digit_sum >= 2 then "1" else "0";
      j := j + 1;
    }
    
    product := new_product;
    i := i + 1;
  }
  
  // Final modulo operation
  var dummy3: string;
  dummy3, res := DivMod(product, sz);
  
  ModExpProperty(Str2Int(sx), Str2Int(sy), Str2Int(sz));
}
// </vc-code>

