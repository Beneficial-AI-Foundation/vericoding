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

// <vc-helpers>
ghost function AddInt(s1: string, s2: string): nat
  requires ValidBitString(s1) && ValidBitString(s2)
  ensures AddInt(s1, s2) == Str2Int(s1) + Str2Int(s2)
{
  Str2Int(s1) + Str2Int(s2)
}

ghost function ModInt(s1: string, s2: string): nat
  requires ValidBitString(s1) && ValidBitString(s2)
  requires Str2Int(s2) > 0
  ensures ModInt(s1, s2) == Str2Int(s1) % Str2Int(s2)
{
  Str2Int(s1) % Str2Int(s2)
}

ghost function Pow2(n: nat): nat
{
  Exp_int(2, n)
}

ghost function Pow2String(n: nat): string
  ensures ValidBitString(Pow2String(n))
  ensures Str2Int(Pow2String(n)) == Pow2(n)
{
  if n == 0 then "1" else Pow2String(n - 1) + "0"
}

method Str2Nat(s: string) returns (n: nat)
  requires ValidBitString(s)
  ensures n == Str2Int(s)
{
  n := 0;
  var i := 0;
  while i < |s|
    invariant 0 <= i <= |s|
    invariant n == Str2Int(s[0..i])
  {
    if s[i] == '1' {
      n := n * 2 + 1;
    } else {
      n := n * 2;
    }
    i := i + 1;
  }
}

method Nat2Str(n: nat) returns (s: string)
  ensures ValidBitString(s)
  ensures Str2Int(s) == n
  ensures n == 0 ==> s == "0"
{
  if n == 0 {
    return "0";
  }
  var bits := "";
  var num := n;
  while num > 0
    invariant num >= 0
    invariant n == num * Pow2(|bits|) + Str2Int(bits)
    invariant ValidBitString(bits)
  {
    var r := num % 2;
    num := num / 2;
    bits := (if r == 1 then "1" else "0") + bits;
  }
  return bits;
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
  var sxVal := Str2Nat(sx);
  var szVal := Str2Nat(sz);
  
  if sxVal % szVal == 0 {
    return "0";
  }
  
  var temp := sxVal % szVal;
  
  if temp == 0 {
    return "0";
  }
  
  var i := 0;
  var current := 1;
  var n := |sy|;
  
  while i < n
    invariant 0 <= i <= n
    invariant current == Exp_int(temp, Str2Int(sy[0..i])) % szVal
    decreases n - i
  {
    current := (current * current) % szVal;
    if sy[i] == '1' {
      current := (current * temp) % szVal;
    }
    i := i + 1;
  }
  
  return Nat2Str(current);
}
// </vc-code>

