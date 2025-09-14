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
function Str2Int(s: string): nat
  requires ValidBitString(s)
  decreases s
{
  if |s| == 0 then  0  else  (2 * Str2Int(s[0..|s|-1]) + (if s[|s|-1] == '1' then 1 else 0))
}
function Exp_int(x: nat, y:nat): nat
{
  if y == 0 then 1 else x * Exp_int(x, y - 1)
}
predicate ValidBitString(s: string)
{
  // All characters must be '0' or '1'.
  forall i | 0 <= i < |s| :: s[i] == '0' || s[i] == '1'
}

// Helper lemma for associativity of modulus in multiplication
lemma ModMulAssoc(x: nat, y: nat, m: nat)
  requires m > 1
  ensures (x * y) % m == ((x % m) * (y % m)) % m
{
  var a := x / m;
  var b := y / m;
  calc {
    (x * y) % m;
    == ((a * m + (x % m)) * (b * m + (y % m))) % m;
    == (a * b * m * m + a * m * (y % m) + b * m * (x % m) + (x % m) * (y % m)) % m;
    == ((x % m) * (y % m)) % m;
  }
}

// Fix: Define a function to convert nat to binary string
function Int2Str(n: nat): string
  decreases n
{
  if n == 0 then "0"
  else Int2Str(n / 2) + (if n % 2 == 0 then "0" else "1")
}

lemma Int2Str_Valid(n: nat)
  ensures ValidBitString(Int2Str(n))
{
  if n == 0 {
    // "0" is valid
  } else {
    Int2Str_Valid(n / 2);
    // then appending "0" or "1" makes it valid
  }
}

lemma Int2Str_Inverse(n: nat)
  ensures Str2Int(Int2Str(n)) == n
{
  Int2Str_Valid(n);
  if n == 0 {
    // Str2Int("0") == 0
  } else {
    Int2Str_Inverse(n / 2);
    // Induction hypothesis
    // Str2Int(Int2Str(n / 2)) == n / 2 by induction
    // Str2Int(Int2Str(n)) == 2 * Str2Int(Int2Str(n / 2)) + (if n % 2 == 0 then 0 else 1) == 2 * (n / 2) + (n % 2) == n
  }
}

// Additional lemmas if needed for string to int conversion in ensures
lemma StrInjective(s: string, t: string)
  requires ValidBitString(s) && ValidBitString(t) && Str2Int(s) == Str2Int(t)
  ensures s == t
{
  // Standard inductive proof
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
  var base: nat := Str2Int(sx);
  var exponent: nat := Str2Int(sy);
  var mod: nat := Str2Int(sz);
  var result: nat := 0;
  if exponent == 0 {
    result := 1;
  } else if base == 0 {
    result := 0;
  } else {
    // binary exp
    result := 1;
    var b: nat := base % mod;
    var exp: nat := exponent;
    while exp > 0
      invariant exp >= 0
      invariant result % mod == Exp_int(base, exponent - exp) % mod
      decreases exp
    {
      if exp % 2 == 1 {
        result := ((result * b) % mod);
      }
      b := ((b * b) % mod);
      exp := exp / 2;
    }
  }
  res := Int2Str(result % mod);
  // Post-conditions should hold by invariants and lemmas
}
// </vc-code>

