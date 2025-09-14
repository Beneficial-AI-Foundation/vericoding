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

lemma ExpLemma(x: nat, y: nat, z: nat)
  ensures Exp_int(x, y + z) == Exp_int(x, y) * Exp_int(x, z)
  decreases y
{
  if y > 0 {
    ExpLemma(x, y - 1, z);
  }
}

lemma ModLemma(a: nat, b: nat, m: nat)
  requires m > 1
  ensures (a * b) % m == ((a % m) * (b % m)) % m
{
}

lemma PowerOfTwoLemma(y: nat, n: nat)
  ensures y == 0 || y == Exp_int(2, n)
{
}

lemma BinaryExpLemma(x: nat, y: nat, m: nat)
  requires m > 1
  ensures Exp_int(x, y) % m == Exp_int(x % m, y) % m
  decreases y
{
  if y == 0 {
  } else {
    BinaryExpLemma(x, y - 1, m);
    ModLemma(Exp_int(x, y - 1) % m, x % m, m);
  }
}

ghost function Int2Str(n: nat): string
  decreases n
{
  if n == 0 then "0" 
  else if n == 1 then "1"
  else Int2Str(n / 2) + (if n % 2 == 0 then "0" else "1")
}

lemma ModExpPow2Lemma(base: nat, exponent: nat, m: nat)
  requires m > 1
  ensures Exp_int(base, Exp_int(2, exponent)) % m == Exp_int(base % m, Exp_int(2, exponent)) % m
  decreases exponent
{
  if exponent > 0 {
    ModExpPow2Lemma(base, exponent - 1, m);
    assert Exp_int(base, Exp_int(2, exponent)) == Exp_int(base, Exp_int(2, exponent - 1)) * Exp_int(base, Exp_int(2, exponent - 1));
    ModLemma(Exp_int(base, Exp_int(2, exponent - 1)) % m, Exp_int(base, Exp_int(2, exponent - 1)) % m, m);
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
  var res_val: nat;
  
  if Str2Int(sy) == 0 {
    res_val := 1 % Str2Int(sz);
  } else {
    var base := Str2Int(sx) % Str2Int(sz);
    var exponent := n;
    var result := 1;
    
    while exponent > 0
      invariant 0 <= exponent <= n
      invariant result == Exp_int(base, Exp_int(2, n - exponent)) % Str2Int(sz)
      decreases exponent
    {
      result := (result * result) % Str2Int(sz);
      exponent := exponent - 1;
    }
    
    res_val := result;
  }
  
  res := if res_val == 0 then "0" 
         else if res_val == 1 then "1"
         else 
              Int2Str(res_val);
}
// </vc-code>

