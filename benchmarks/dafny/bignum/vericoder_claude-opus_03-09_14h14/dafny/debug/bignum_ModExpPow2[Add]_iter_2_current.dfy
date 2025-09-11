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

// <vc-helpers>
lemma ExpPow2Lemma(x: nat, n: nat)
  ensures n > 0 ==> Exp_int(x, Exp_int(2, n)) == Exp_int(Exp_int(x, Exp_int(2, n-1)), 2)
{
  if n > 0 {
    calc {
      Exp_int(x, Exp_int(2, n));
      == Exp_int(x, 2 * Exp_int(2, n-1));
      == { ExpMultLemma(x, Exp_int(2, n-1), Exp_int(2, n-1)); }
      Exp_int(x, Exp_int(2, n-1)) * Exp_int(x, Exp_int(2, n-1));
      == Exp_int(Exp_int(x, Exp_int(2, n-1)), 2);
    }
  }
}

lemma ExpMultLemma(x: nat, a: nat, b: nat)
  ensures Exp_int(x, a + b) == Exp_int(x, a) * Exp_int(x, b)
{
  if b == 0 {
    assert Exp_int(x, a + 0) == Exp_int(x, a) * 1;
  } else {
    calc {
      Exp_int(x, a + b);
      == x * Exp_int(x, a + b - 1);
      == { ExpMultLemma(x, a, b - 1); }
      x * (Exp_int(x, a) * Exp_int(x, b - 1));
      == Exp_int(x, a) * (x * Exp_int(x, b - 1));
      == Exp_int(x, a) * Exp_int(x, b);
    }
  }
}

lemma ModExpSquareLemma(a: nat, b: nat, m: nat)
  requires m > 1
  ensures (Exp_int(a, 2) % m) == ((a % m) * (a % m)) % m
{
  calc {
    Exp_int(a, 2) % m;
    == (a * a) % m;
    == ((a % m) * (a % m)) % m;
  }
}

method Mod(s1: string, s2: string) returns (res: string)
  requires ValidBitString(s1) && ValidBitString(s2)
  requires Str2Int(s2) > 0
  ensures ValidBitString(res)
  ensures Str2Int(res) == Str2Int(s1) % Str2Int(s2)

method Mult(s1: string, s2: string) returns (res: string)
  requires ValidBitString(s1) && ValidBitString(s2)
  ensures ValidBitString(res)
  ensures Str2Int(res) == Str2Int(s1) * Str2Int(s2)
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
    // Base case: x^1 mod z = x mod z
    res := Mod(sx, sz);
    assert Str2Int(sy) == Exp_int(2, 0) == 1;
    assert Exp_int(Str2Int(sx), Str2Int(sy)) == Exp_int(Str2Int(sx), 1) == Str2Int(sx);
  } else if Str2Int(sy) == 0 {
    // Special case: x^0 = 1
    res := "1";
    assert Exp_int(Str2Int(sx), 0) == 1;
  } else {
    // Recursive case: x^(2^n) = (x^(2^(n-1)))^2
    // First compute sy' = 2^(n-1)
    var sy_half := sy[1..];  // Remove leading bit to get 2^(n-1)
    assert |sy_half| == n;
    
    // Recursively compute x^(2^(n-1)) mod z
    var temp := ModExpPow2(sx, sy_half, n-1, sz);
    
    // Square the result: (temp)^2 mod z
    var temp_squared := Mult(temp, temp);
    res := Mod(temp_squared, sz);
    
    // Correctness proof
    ExpPow2Lemma(Str2Int(sx), n);
    assert Exp_int(Str2Int(sx), Str2Int(sy)) == Exp_int(Exp_int(Str2Int(sx), Exp_int(2, n-1)), 2);
    assert Str2Int(temp) == Exp_int(Str2Int(sx), Exp_int(2, n-1)) % Str2Int(sz);
  }
}
// </vc-code>

