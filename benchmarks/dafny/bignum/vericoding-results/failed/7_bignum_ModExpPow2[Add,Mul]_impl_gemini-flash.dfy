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

method Mul(s1: string, s2: string) returns (res: string)
  requires ValidBitString(s1) && ValidBitString(s2)
  ensures ValidBitString(res)
  ensures Str2Int(res) == Str2Int(s1) * Str2Int(s2)
{
  assume{:axiom} false;
}

// <vc-helpers>
function int2BitString(n: nat): string
{
  if n == 0 then
    "0"
  else if n == 1 then
    "1"
  else
    (if n / 2 == 0 then "" else int2BitString(n / 2)) + (if n % 2 == 0 then "0" else "1")
}

// Helper to prove Str2Int(int2BitString(n)) == n
lemma int2BitString_Str2Int_identity(n: nat)
  ensures Str2Int(int2BitString(n)) == n
  decreases n
{
  if n == 0 {
  } else if n == 1 {
  } else {
    int2BitString_Str2Int_identity(n / 2);
  }
}

// Helper to prove ValidBitString for int2BitString
lemma ValidBitString_int2BitString(n: nat)
  ensures ValidBitString(int2BitString(n))
  decreases n
{
  if n == 0 {
  } else if n == 1 {
  } else {
    ValidBitString_int2BitString(n / 2);
  }
}

// Helper for modulus property
lemma ModuloProperty(a: nat, b: nat, c:nat)
  requires c > 0
  ensures (a * b) % c == ((a % c) * (b % c)) % c
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
  var x_val := Str2Int(sx);
  var y_val := Str2Int(sy);
  var z_val := Str2Int(sz);

  if y_val == 0 {
    var one_mod_z := (1 % z_val);
    ValidBitString_int2BitString(one_mod_z);
    int2BitString_Str2Int_identity(one_mod_z);
    res := int2BitString(one_mod_z);
  } else if y_val == 1 {
    var x_mod_z := (x_val % z_val);
    ValidBitString_int2BitString(x_mod_z);
    int2BitString_Str2Int_identity(x_mod_z);
    res := int2BitString(x_mod_z);
  } else {
    // y_val = 2^n for n > 0
    // y_val is even, so sy ends with '0'
    // sy does not change, n decreases so sy for recursive call is shorter
    // sy = sy_prefix + '0'
    var half_sy_str := sy[0..|sy|-1]; 
    var recursive_result_str: string := ModExpPow2(sx, half_sy_str, n - 1, sz);
    var recursive_result_val := Str2Int(recursive_result_str);

    // We want to compute (x^y) % z = (x^(2*k)) % z = ((x^k)^2) % z
    // Here y = 2k, so k = y/2.
    // x^k is computed by the recursive call, which returns (x^(y/2)) % z.
    // Let r = (x^(y/2)) % z. We need to compute (r * r) % z.

    ModuloProperty(recursive_result_val, recursive_result_val, z_val);
    var final_val := (recursive_result_val * recursive_result_val) % z_val;
    ValidBitString_int2BitString(final_val);
    int2BitString_Str2Int_identity(final_val);
    res := int2BitString(final_val);
  }
}
// </vc-code>

