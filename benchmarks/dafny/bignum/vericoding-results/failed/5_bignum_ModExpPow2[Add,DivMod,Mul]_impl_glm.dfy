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
function method ModExpPow2Helper(x: nat, y: nat, modulus: nat, n: nat): nat
  requires y == Exp_int(2, n) || y == 0
  requires modulus > 1
  ensures ModExpPow2Helper(x, y, modulus, n) == Exp_int(x, y) % modulus
  decreases n
{
  if y == 0 then 1 % modulus
  else if n == 0 then x % modulus
  else
    let half := ModExpPow2Helper(x, 1 << (n-1), modulus, n-1) in
    (half * half) % modulus
}

function NatToStr2Int(n: nat): string
  ensures ValidBitString(NatToStr2Int(n))
  ensures Str2Int(NatToStr2Int(n)) == n
  decreases n
{
  if n == 0 then "0"
  else if n == 1 then "1"
  else
    var prev := NatToStr2Int(n / 2);
    if n % 2 == 0 then prev + "0" else prev + "1"
}

lemma NatToStr2IntValid(n: nat)
  ensures ValidBitString(NatToStr2Int(n))
  ensures Str2Int(NatToStr2Int(n)) == n
  decreases n
{
  if n == 0 {
    calc {
      Str2Int(NatToStr2Int(0));
      == { reveal NatToStr2Int; }
      Str2Int("0");
      == { reveal Str2Int; }
      0;
    }
  } else if n == 1 {
    calc {
      Str2Int(NatToStr2Int(1));
      == { reveal NatToStr2Int; }
      Str2Int("1");
      == { reveal Str2Int; }
      2 * Str2Int("") + (if '1' == '1' then 1 else 0);
      == { assert Str2Int("") == 0; }
      2 * 0 + 1;
      == 1;
    }
  } else {
    NatToStr2IntValid(n / 2);
    var half_str := NatToStr2Int(n / 2);
    calc {
      Str2Int(NatToStr2Int(n));
      == { reveal NatToStr2Int; }
      Str2Int(if n % 2 == 0 then half_str + "0" else half_str + "1");
      == { reveal Str2Int; }
      2 * Str2Int(half_str) + (if n % 2 == 0 then 0 else 1);
      == { NatToStr2IntValid(n/2); }
      2 * (n/2) + (if n % 2 == 0 then 0 else 1);
      == 
      n;
    }
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
  var x := Str2Int(sx);
  var y := Str2Int(sy);
  var modulus := Str2Int(sz);
  res := NatToStr2Int(ModExpPow2Helper(x, y, modulus, n));
}
// </vc-code>

