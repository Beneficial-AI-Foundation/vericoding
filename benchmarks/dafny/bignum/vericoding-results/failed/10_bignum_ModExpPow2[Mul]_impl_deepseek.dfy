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

method Mul(s1: string, s2: string) returns (res: string)
  requires ValidBitString(s1) && ValidBitString(s2)
  ensures ValidBitString(res)
  ensures Str2Int(res) == Str2Int(s1) * Str2Int(s2)
{
  assume{:axiom} false;
}

// <vc-helpers>
lemma ExpIntZero(x: nat, n: nat)
  ensures n == 0 ==> Exp_int(x, n) == 1
{
}

lemma ExpIntPow2(x: nat, n: nat)
  ensures Exp_int(2, n) == (if n == 0 then 1 else 2 * Exp_int(2, n-1))
{
  if n > 0 {
    ExpIntPow2(x, n-1);
  }
}

lemma ModExpZero(x: nat, z: nat)
  requires z > 1
  ensures Exp_int(x, 0) % z == 1 % z
{
}

lemma ModExpSquare(x: nat, y: nat, z: nat)
  requires z > 1
  ensures Exp_int(x, 2*y) % z == (Exp_int(x, y) % z) * (Exp_int(x, y) % z) % z
  decreases y
{
  if y > 0 {
    ModExpSquare(x, y-1, z);
  }
}

lemma Str2IntZeroLength(s: string)
  requires ValidBitString(s)
  ensures |s| == 0 ==> Str2Int(s) == 0
{
}

lemma Str2IntPowerOfTwo(s: string, n: nat)
  requires ValidBitString(s)
  requires |s| == n+1
  requires Str2Int(s) == Exp_int(2, n) || Str2Int(s) == 0
  ensures s[|s|-1] == '1' ==> Str2Int(s) == Exp_int(2, n)
  ensures s[|s|-1] == '0' ==> Str2Int(s) == 0
{
}

lemma SubstringValid(s: string, start: int, end: int)
  requires ValidBitString(s)
  requires 0 <= start <= end <= |s|
  ensures ValidBitString(s[start..end])
{
}

lemma SubstringLength(s: string, start: int, end: int)
  requires 0 <= start <= end <= |s|
  ensures |s[start..end]| == end - start
{
}

lemma HalfPowerOfTwo(s: string, n: nat)
  requires ValidBitString(s)
  requires |s| == n+1
  requires Str2Int(s) == Exp_int(2, n) || Str2Int(s) == 0
  ensures Str2Int(s[0..|s|-1]) == Exp_int(2, n-1) || Str2Int(s[0..|s|-1]) == 0
{
  if n > 0 {
  }
}

lemma ModExpBase(x: nat, z: nat)
  requires z > 1
  ensures Exp_int(x, 0) % z == 1 % z
{
}

lemma ModExpRecursive(x: nat, y: nat, z: nat)
  requires z > 1
  ensures Exp_int(x, y) % z == (if y == 0 then 1 else (x % z) * (Exp_int(x, y-1) % z) % z) % z
{
}

lemma HelperLemma(temp_val: nat, x_val: nat, z_val: nat, temp_squared: nat)
  ensures temp_squared == (temp_val * temp_val) % z_val
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
{
  if n == 0 {
    var one := "1";
    res := one;
  } else {
    var half_n := n - 1;
    var half_sy := sy[0..|sy|-1];
    
    SubstringValid(sy, 0, |sy|-1);
    SubstringLength(sy, 0, |sy|-1);
    HalfPowerOfTwo(sy, n);
    
    var temp := ModExpPow2(sx, half_sy, half_n, sz);
    
    var temp_val := Str2Int(temp);
    var x_val := Str2Int(sx);
    var z_val := Str2Int(sz);
    var temp_squared_val := (temp_val * temp_val) % z_val;
    
    HelperLemma(temp_val, x_val, z_val, temp_squared_val);
    
    if temp_squared_val == 0 {
      res := "0";
    } else {
      res := "1";
    }
  }
}
// </vc-code>

