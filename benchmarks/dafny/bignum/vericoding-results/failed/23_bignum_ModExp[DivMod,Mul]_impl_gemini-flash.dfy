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

method Mul(s1: string, s2: string) returns (res: string)
  requires ValidBitString(s1) && ValidBitString(s2)
  ensures ValidBitString(res)
  ensures Str2Int(res) == Str2Int(s1) * Str2Int(s2)
{
  assume{:axiom} false;
}

// <vc-helpers>
function Pow2(n: nat): nat
  decreases n
{
  if n == 0 then 1 else 2 * Pow2(n-1)
}

function StrRev(s: string): string {
  if |s| == 0 then ""
  else (StrRev(s[1..])) + s[0..1]
}

function AppendDigit(s: string, d: char): string
  requires d == '0' || d == '1'
{
  s + d
}

function CharToInt(c: char): int
  requires c == '0' || c == '1'
{
  if c == '0' then 0 else 1
}

function StringToBitArray(s: string): seq<int>
  requires ValidBitString(s)
  ensures forall i :: 0 <= i < |s| ==> (StringToBitArray(s)[i] == 0 || StringToBitArray(s)[i] == 1)
{
  if |s| == 0 then []
  else StringToBitArray(s[0 .. |s|-1]) + [CharToInt(s[|s|-1])]
}

ghost predicate Str2IntLemma(s: string, n: nat)
  requires ValidBitString(s)
  requires n == |s|
{
  (Str2Int(s) == (if n == 0 then 0 else Str2Int(s[0..n-1]) * 2 + CharToInt(s[n-1])))
}

lemma Str2IntPrefixLemma(s: string, k: nat)
  requires ValidBitString(s)
  requires 0 <= k <= |s|
  ensures Str2Int(s[0..k]) == Str2Int(s) / Pow2(|s|-k)
  // This lemma is a bit more complex than needed for this specific problem,
  // but it's a general property of Str2Int.
{
  if k < |s| {
    Str2IntPrefixLemma(s, k+1);
    calc {
      Str2Int(s);
      Str2Int(s[0..|s|-1]) * 2 + CharToInt(s[|s|-1]);
      (Str2Int(s[0..k]) * Pow2(|s|-1-k)) * 2 + CharToInt(s[|s|-1]);
      {
        assert Pow2(|s|-1-k) * 2 == Pow2(|s|-k);
      }
      Str2Int(s[0..k]) * Pow2(|s|-k) + CharToInt(s[|s|-1]);
    }
  } else {
    assert k == |s|;
    assert Pow2(|s|-k) == Pow2(0) == 1;
    assert Str2Int(s[0..k]) == Str2Int(s) / 1;
  }
}

lemma Str2IntEmptyStringIsZero()
  ensures Str2Int("") == 0
{}

lemma Str2IntSingleBit(s: string)
  requires ValidBitString(s)
  requires |s| == 1
  ensures Str2Int(s) == CharToInt(s[0])
{}

function ToBinary(n: nat): string
  ensures ValidBitString(ToBinary(n))
  ensures Str2Int(ToBinary(n)) == n
  decreases n
{
  if n == 0 then "0"
  else ToBinaryNonZero(n)
}

function ToBinaryNonZero(n: nat): string
  requires n > 0
  ensures ValidBitString(ToBinaryNonZero(n))
  ensures Str2Int(ToBinaryNonZero(n)) == n
  decreases n
{
  if n == 1 then "1"
  else ToBinaryNonZero(n / 2) + (if n % 2 == 0 then "0" else "1")
}

lemma theorem_int_lemma(a: int, b: int, c: int)
  requires b > 0
  ensures (a * b + c) % b == c % b
{
}
// Helper lemma to prove `Exp_int(x, a) % z == Exp_int(x % z, a) % z`
lemma ModuloExponentEquivalence(x: nat, a: nat, z: nat)
  requires z > 0
  ensures Exp_int(x, a) % z == Exp_int(x % z, a) % z
  decreases a
{
  if a == 0 {
    assert Exp_int(x, 0) % z == 1 % z;
    assert Exp_int(x % z, 0) % z == 1 % z;
  } else {
    ModuloExponentEquivalence(x, a - 1, z);
    calc {
      Exp_int(x, a) % z;
      (x * Exp_int(x, a - 1)) % z;
      ((x % z) * (Exp_int(x, a - 1) % z)) % z; // Property of modular arithmetic: (a*b)%m = ((a%m)*(b%m))%m
      ((x % z) * (Exp_int(x % z, a - 1) % z)) % z;
      ((x % z) * (Exp_int(x % z, a - 1))) % z;
      Exp_int(x % z, a) % z;
    }
  }
}

lemma Exp_int_property(x: nat, k: nat)
  requires k > 0
  ensures Exp_int(x, k) == x * Exp_int(x, k-1)
{}

lemma Exp_int_even(b: nat, e: nat)
  requires e > 0
  ensures Exp_int(b, e) == Exp_int(b * b, e / 2) * (if e % 2 == 1 then b else 1)
  decreases e
{
  if e == 1 {
    calc {
      Exp_int(b, 1);
      b;
      Exp_int(b * b, 1 / 2) * b;
      Exp_int(b * b, 0) * b;
      1 * b;
    }
  } else if e % 2 == 0 {
    Exp_int_even(b, e / 2);
    calc {
      Exp_int(b, e);
      Exp_int(b * b, e / 2);
    }
  } else {
    Exp_int_even(b, e / 2);
    calc {
      Exp_int(b, e);
      b * Exp_int(b, e - 1);
      b * Exp_int(b * b, (e - 1) / 2);
      b * Exp_int(b * b, e / 2);
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
   var x_val := Str2Int(sx);
   var y_val := Str2Int(sy);
   var z_val := Str2Int(sz);

   if y_val == 0 {
     return "1"; // x^0 is 1
   }

   var res_val: nat := 1;
   var base_val: nat := x_val % z_val;
   var exp_val: nat := y_val;

   while exp_val > 0
     invariant Exp_int(x_val, y_val) % z_val == (res_val * Exp_int(base_val, exp_val)) % z_val
     invariant base_val < z_val
     invariant z_val > 1
     invariant exp_val >= 0
     decreases exp_val
   {
     if exp_val % 2 == 1 {
       res_val := (res_val * base_val) % z_val;
     }

     if exp_val / 2 > 0 { // Removed z_val > 0 check as it's guaranteed by invariant
        ModuloExponentEquivalence(base_val, exp_val / 2, z_val);
     }
     base_val := (base_val * base_val) % z_val;
     exp_val := exp_val / 2;
   }
   return ToBinary(res_val);
}
// </vc-code>

