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

// <vc-helpers>
lemma ExpPow2Squared(x: nat, n: nat)
  requires n > 0
  ensures Exp_int(x, Exp_int(2, n)) == Exp_int(Exp_int(x, Exp_int(2, n-1)), 2)
{
  calc {
    Exp_int(x, Exp_int(2, n));
    == Exp_int(x, 2 * Exp_int(2, n-1));
    == { ExpMultiply(x, Exp_int(2, n-1), Exp_int(2, n-1)); }
    Exp_int(x, Exp_int(2, n-1)) * Exp_int(x, Exp_int(2, n-1));
    == Exp_int(Exp_int(x, Exp_int(2, n-1)), 2);
  }
}

lemma ExpMultiply(x: nat, a: nat, b: nat)
  ensures Exp_int(x, a + b) == Exp_int(x, a) * Exp_int(x, b)
{
  if b == 0 {
    assert Exp_int(x, a + 0) == Exp_int(x, a) * 1;
  } else {
    calc {
      Exp_int(x, a + b);
      == x * Exp_int(x, a + b - 1);
      == { ExpMultiply(x, a, b - 1); }
      x * (Exp_int(x, a) * Exp_int(x, b - 1));
      == Exp_int(x, a) * (x * Exp_int(x, b - 1));
      == Exp_int(x, a) * Exp_int(x, b);
    }
  }
}

lemma ModExpSquared(a: nat, b: nat, m: nat)
  requires m > 0
  ensures (a * a) % m == ((a % m) * (a % m)) % m
{
}

method PowerOfTwoString(n: nat) returns (s: string)
  ensures ValidBitString(s)
  ensures |s| == n + 1
  ensures Str2Int(s) == Exp_int(2, n)
{
  if n == 0 {
    s := "1";
  } else {
    s := "1";
    var i := 0;
    while i < n
      invariant 0 <= i <= n
      invariant |s| == i + 1
      invariant ValidBitString(s)
      invariant Str2Int(s) == Exp_int(2, i)
    {
      s := s + "0";
      i := i + 1;
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
  if n == 0 {
    // sy is either 0 or 1 (2^0 = 1)
    // Check if sy is "0" (all zeros)
    var isZero := true;
    var i := 0;
    while i < |sy|
      invariant 0 <= i <= |sy|
      invariant isZero ==> forall j :: 0 <= j < i ==> sy[j] == '0'
    {
      if sy[i] != '0' {
        isZero := false;
      }
      i := i + 1;
    }
    
    if isZero {
      // x^0 = 1
      var q, r := DivMod("1", sz);
      res := r;
    } else {
      // sy = 1, so x^1 = x
      var q, r := DivMod(sx, sz);
      res := r;
    }
  } else {
    // sy = 2^n for n > 0
    // Compute x^(2^(n-1)) mod z recursively
    var halfPower := PowerOfTwoString(n-1);
    
    var temp := ModExpPow2(sx, halfPower, n-1, sz);
    
    // Square the result: (x^(2^(n-1)))^2 mod z
    // Compute temp * temp
    var product := "0";
    var j := 0;
    
    while j < |temp|
      invariant 0 <= j <= |temp|
      invariant ValidBitString(product)
    {
      var k := 0;
      while k < |temp|
        invariant 0 <= k <= |temp|
        invariant ValidBitString(product)
      {
        if temp[j] == '1' && temp[k] == '1' {
          // Add contribution for bit position j+k
          var shiftAmount := j + k;
          var contribution := "1";
          var s := 0;
          while s < shiftAmount
            invariant 0 <= s <= shiftAmount
            invariant ValidBitString(contribution)
            invariant |contribution| == s + 1
          {
            contribution := contribution + "0";
            s := s + 1;
          }
          product := Add(product, contribution);
        }
        k := k + 1;
      }
      j := j + 1;
    }
    
    ExpPow2Squared(Str2Int(sx), n);
    var q, r := DivMod(product, sz);
    res := r;
  }
}
// </vc-code>

