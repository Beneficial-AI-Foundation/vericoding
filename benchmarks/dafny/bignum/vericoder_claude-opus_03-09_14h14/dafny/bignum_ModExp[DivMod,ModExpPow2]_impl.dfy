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
  assert Exp_int(x, y) == x * Exp_int(x, y - 1);
}

lemma ModExpEvenProperty(x: nat, y: nat, z: nat)
  requires z > 0
  requires y > 0 && y % 2 == 0
  ensures Exp_int(x, y) % z == (Exp_int(x, y/2) % z * Exp_int(x, y/2) % z) % z
{
  var half := y / 2;
  assert y == 2 * half;
  assert Exp_int(x, y) == Exp_int(x, 2 * half);
  
  var i := half;
  while i > 0
    invariant 0 <= i <= half
    invariant Exp_int(x, half + (half - i)) == Exp_int(x, half) * Exp_int(x, half - i)
  {
    i := i - 1;
  }
  assert Exp_int(x, 2 * half) == Exp_int(x, half) * Exp_int(x, half);
}

lemma ModExpOddProperty(x: nat, y: nat, z: nat)
  requires z > 0
  requires y > 0 && y % 2 == 1
  ensures Exp_int(x, y) % z == ((Exp_int(x, y/2) % z * Exp_int(x, y/2) % z) % z * (x % z)) % z
{
  var half := y / 2;
  assert y == 2 * half + 1;
  ModExpEvenProperty(x, 2 * half, z);
  assert Exp_int(x, y) == Exp_int(x, 2 * half + 1);
  assert Exp_int(x, 2 * half + 1) == Exp_int(x, 2 * half) * x;
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

lemma Str2IntTwoString()
  ensures ValidBitString("10")
  ensures Str2Int("10") == 2
{
  assert Str2Int("10") == 2 * Str2Int("1") + 0 == 2 * 1 + 0 == 2;
}

lemma Str2IntAllZeros(s: string)
  requires ValidBitString(s)
  requires forall i | 0 <= i < |s| :: s[i] == '0'
  ensures Str2Int(s) == 0
  decreases |s|
{
  if |s| == 0 {
  } else {
    var prefix := s[0..|s|-1];
    assert forall i | 0 <= i < |prefix| :: prefix[i] == '0';
    Str2IntAllZeros(prefix);
    assert s[|s|-1] == '0';
    assert Str2Int(s) == 2 * Str2Int(prefix) + 0;
    assert Str2Int(s) == 0;
  }
}

lemma Str2IntHasOne(s: string)
  requires ValidBitString(s)
  requires exists i | 0 <= i < |s| :: s[i] == '1'
  ensures Str2Int(s) > 0
  decreases |s|
{
  if |s| == 0 {
    assert false;
  } else if s[|s|-1] == '1' {
    assert Str2Int(s) == 2 * Str2Int(s[0..|s|-1]) + 1;
    assert Str2Int(s) >= 1;
  } else {
    var prefix := s[0..|s|-1];
    assert exists i | 0 <= i < |prefix| :: prefix[i] == '1';
    Str2IntHasOne(prefix);
    assert Str2Int(s) == 2 * Str2Int(prefix) + 0;
    assert Str2Int(s) > 0;
  }
}

method IsAllZeros(s: string) returns (allZeros: bool)
  requires ValidBitString(s)
  ensures allZeros <==> (forall i | 0 <= i < |s| :: s[i] == '0')
  ensures allZeros ==> Str2Int(s) == 0
{
  allZeros := true;
  var i := 0;
  while i < |s|
    invariant 0 <= i <= |s|
    invariant allZeros <==> (forall j | 0 <= j < i :: s[j] == '0')
  {
    if s[i] != '0' {
      allZeros := false;
      break;
    }
    i := i + 1;
  }
  if allZeros {
    Str2IntAllZeros(s);
  }
}

method StringMul(a: string, b: string) returns (result: string)
  requires ValidBitString(a) && ValidBitString(b)
  ensures ValidBitString(result)
  ensures Str2Int(result) == Str2Int(a) * Str2Int(b)
{
  result := "0";
  var temp := b;
  var shift := a;
  
  while temp != "0"
    invariant ValidBitString(temp)
    invariant ValidBitString(shift)
    invariant ValidBitString(result)
    decreases Str2Int(temp)
  {
    if |temp| > 0 && temp[|temp|-1] == '1' {
      result := StringAdd(result, shift);
    }
    shift := shift + "0";
    temp := if |temp| > 1 then temp[0..|temp|-1] else "0";
  }
}

method StringAdd(a: string, b: string) returns (result: string)
  requires ValidBitString(a) && ValidBitString(b)
  ensures ValidBitString(result)
  ensures Str2Int(result) == Str2Int(a) + Str2Int(b)
{
  result := "0";
  var carry := false;
  var i := 0;
  var maxLen := if |a| > |b| then |a| else |b|;
  
  while i < maxLen || carry
    invariant ValidBitString(result)
  {
    var bitA := if i < |a| then (if a[|a|-1-i] == '1' then 1 else 0) else 0;
    var bitB := if i < |b| then (if b[|b|-1-i] == '1' then 1 else 0) else 0;
    var sum := bitA + bitB + (if carry then 1 else 0);
    
    result := (if sum % 2 == 1 then "1" else "0") + result;
    carry := sum >= 2;
    i := i + 1;
  }
  
  if result == "" {
    result := "0";
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
  var isZero := IsAllZeros(sy);
  if isZero {
    Str2IntOneString();
    res := "1";
  } else {
    Str2IntHasOne(sy);
    Str2IntTwoString();
    
    var y_div_2_str, y_mod_2_str := DivMod(sy, "10");
    
    var half_exp := ModExp(sx, y_div_2_str, sz);
    
    var squared := StringMul(half_exp, half_exp);
    var squared_mod, _ := DivMod(squared, sz);
    
    if y_mod_2_str == "1" {
      var x_mod_z, _ := DivMod(sx, sz);
      var product := StringMul(squared_mod, x_mod_z);
      var final_mod, _ := DivMod(product, sz);
      res := final_mod;
      
      ModExpOddProperty(Str2Int(sx), Str2Int(sy), Str2Int(sz));
    } else {
      res := squared_mod;
      
      ModExpEvenProperty(Str2Int(sx), Str2Int(sy), Str2Int(sz));
    }
  }
}
// </vc-code>

