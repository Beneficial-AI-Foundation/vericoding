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
lemma ExpPow2Lemma(x: nat, n: nat)
  ensures n > 0 ==> Exp_int(x, Exp_int(2, n)) == Exp_int(Exp_int(x, Exp_int(2, n-1)), 2)
{
  if n > 0 {
    calc {
      Exp_int(x, Exp_int(2, n));
      == Exp_int(x, 2 * Exp_int(2, n-1));
      == { ExpMultLemma(x, 2, Exp_int(2, n-1)); }
      Exp_int(Exp_int(x, 2), Exp_int(2, n-1));
      == { ExpExpLemma(x, 2, Exp_int(2, n-1)); }
      Exp_int(Exp_int(x, Exp_int(2, n-1)), 2);
    }
  }
}

lemma ExpMultLemma(x: nat, a: nat, b: nat)
  ensures Exp_int(x, a * b) == Exp_int(Exp_int(x, a), b)
  decreases b
{
  if b == 0 {
    assert a * b == 0;
    assert Exp_int(x, 0) == 1;
    assert Exp_int(Exp_int(x, a), 0) == 1;
  } else {
    calc {
      Exp_int(x, a * b);
      == x * Exp_int(x, a * b - 1);
      == { assert a * b - 1 == a * (b - 1) + (a - 1); }
      x * Exp_int(x, a * (b - 1) + (a - 1));
      == { if a > 0 { ExpAddLemma(x, a * (b - 1), a - 1); } else { assert a == 0; assert a * (b - 1) + (a - 1) == 0; } }
      x * Exp_int(x, a * (b - 1)) * Exp_int(x, a - 1);
      == { ExpMultLemma(x, a, b - 1); }
      x * Exp_int(Exp_int(x, a), b - 1) * Exp_int(x, a - 1);
      == { if a > 0 { assert Exp_int(x, a) == x * Exp_int(x, a - 1); } else { assert a == 0; assert Exp_int(x, 0) == 1; assert Exp_int(x, a - 1) == 1; } }
      Exp_int(x, a) * Exp_int(Exp_int(x, a), b - 1);
      == Exp_int(Exp_int(x, a), b);
    }
  }
}

lemma ExpAddLemma(x: nat, a: nat, b: nat)
  ensures Exp_int(x, a + b) == Exp_int(x, a) * Exp_int(x, b)
  decreases b
{
  if b == 0 {
    assert Exp_int(x, b) == 1;
    assert Exp_int(x, a + 0) == Exp_int(x, a) * 1;
  } else {
    calc {
      Exp_int(x, a + b);
      == x * Exp_int(x, a + b - 1);
      == x * Exp_int(x, a + (b - 1));
      == { ExpAddLemma(x, a, b - 1); }
      x * Exp_int(x, a) * Exp_int(x, b - 1);
      == Exp_int(x, a) * (x * Exp_int(x, b - 1));
      == Exp_int(x, a) * Exp_int(x, b);
    }
  }
}

lemma ExpExpLemma(x: nat, a: nat, b: nat)
  ensures Exp_int(Exp_int(x, a), b) == Exp_int(x, a * b)
{
  ExpMultLemma(x, a, b);
}

lemma ModExpLemma(a: nat, b: nat, m: nat)
  requires m > 0
  ensures Exp_int(a % m, b) % m == Exp_int(a, b) % m
  decreases b
{
  if b == 0 {
    assert Exp_int(a % m, 0) == 1;
    assert Exp_int(a, 0) == 1;
  } else {
    calc {
      Exp_int(a % m, b) % m;
      == ((a % m) * Exp_int(a % m, b - 1)) % m;
      == { ModMultLemma(a % m, Exp_int(a % m, b - 1), m); }
      ((a % m) * (Exp_int(a % m, b - 1) % m)) % m;
      == { ModExpLemma(a, b - 1, m); }
      ((a % m) * (Exp_int(a, b - 1) % m)) % m;
      == { ModMultLemma(a, Exp_int(a, b - 1), m); }
      (a * Exp_int(a, b - 1)) % m;
      == Exp_int(a, b) % m;
    }
  }
}

lemma ModMultLemma(a: nat, b: nat, m: nat)
  requires m > 0
  ensures (a * b) % m == ((a % m) * (b % m)) % m
{
  // This is a standard modular arithmetic property
}

function method IntToString(n: nat): string
  ensures ValidBitString(IntToString(n))
  ensures Str2Int(IntToString(n)) == n
  decreases n
{
  if n == 0 then "0"
  else if n == 1 then "1"
  else IntToString(n / 2) + (if n % 2 == 0 then "0" else "1")
}

predicate AllZeros(s: string)
{
  forall i | 0 <= i < |s| :: s[i] == '0'
}

lemma AllZerosImpliesZero(s: string)
  requires ValidBitString(s)
  requires AllZeros(s)
  ensures Str2Int(s) == 0
{
  if |s| == 0 {
    assert Str2Int(s) == 0;
  } else {
    assert s[|s|-1] == '0';
    AllZerosImpliesZero(s[0..|s|-1]);
    assert Str2Int(s) == 2 * Str2Int(s[0..|s|-1]) + 0;
  }
}

lemma ZeroImpliesAllZeros(s: string)
  requires ValidBitString(s)
  requires Str2Int(s) == 0
  requires |s| > 0
  ensures AllZeros(s)
{
  if |s| == 1 {
    if s[0] == '1' {
      assert Str2Int(s) == 1;
      assert false;
    }
  } else {
    assert Str2Int(s) == 2 * Str2Int(s[0..|s|-1]) + (if s[|s|-1] == '1' then 1 else 0);
    if s[|s|-1] == '1' {
      assert Str2Int(s) >= 1;
      assert false;
    }
    assert Str2Int(s[0..|s|-1]) == 0;
    if |s[0..|s|-1]| > 0 {
      ZeroImpliesAllZeros(s[0..|s|-1]);
    }
  }
}

lemma Str2IntPrefixLemma(s: string)
  requires ValidBitString(s)
  requires |s| > 0
  ensures Str2Int(s) == 2 * Str2Int(s[0..|s|-1]) + (if s[|s|-1] == '1' then 1 else 0)
{
  // This follows directly from the definition of Str2Int
}

lemma ShiftLeftZeroLemma(s: string)
  requires ValidBitString(s)
  ensures Str2Int("0" + s) == Str2Int(s)
{
  if |s| == 0 {
    assert Str2Int("0") == 0;
    assert Str2Int(s) == 0;
  } else {
    var t := "0" + s;
    calc {
      Str2Int("0" + s);
      == 2 * Str2Int(("0" + s)[0..|"0" + s|-1]) + (if ("0" + s)[|"0" + s|-1] == '1' then 1 else 0);
      == 2 * Str2Int("0" + s[0..|s|-1]) + (if s[|s|-1] == '1' then 1 else 0);
      == { ShiftLeftZeroLemma(s[0..|s|-1]); }
      2 * Str2Int(s[0..|s|-1]) + (if s[|s|-1] == '1' then 1 else 0);
      == Str2Int(s);
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
  var isZero := true;
  var i := 0;
  while i < |sy|
    invariant 0 <= i <= |sy|
    invariant isZero == (forall j | 0 <= j < i :: sy[j] == '0')
  {
    if sy[i] != '0' {
      isZero := false;
    }
    i := i + 1;
  }
  
  if isZero {
    res := "1";
    assert AllZeros(sy);
    AllZerosImpliesZero(sy);
    assert Str2Int(sy) == 0;
    assert Exp_int(Str2Int(sx), 0) == 1;
  } else if n == 0 {
    assert !AllZeros(sy);
    assert |sy| == 1;
    assert sy[0] != '0';
    assert sy[0] == '1';
    assert Str2Int(sy) == 1;
    var q, r := DivMod(sx, sz);
    res := r;
    assert Str2Int(res) == Str2Int(sx) % Str2Int(sz);
    assert Exp_int(Str2Int(sx), 1) == Str2Int(sx);
  } else {
    assert !AllZeros(sy);
    assert Str2Int(sy) != 0;
    assert Str2Int(sy) == Exp_int(2, n);
    
    var sy_half := sy[0..|sy|-1];
    assert |sy_half| == n;
    
    assert Str2Int(sy) == Exp_int(2, n);
    assert Exp_int(2, n) == 2 * Exp_int(2, n-1);
    Str2IntPrefixLemma(sy);
    assert Str2Int(sy) == 2 * Str2Int(sy[0..|sy|-1]) + (if sy[|sy|-1] == '1' then 1 else 0);
    assert sy[|sy|-1] == '0';
    assert Str2Int(sy) == 2 * Str2Int(sy_half);
    assert Str2Int(sy_half) == Exp_int(2, n-1);
    
    var temp := ModExpPow2(sx, sy_half, n-1, sz);
    assert Str2Int(temp) == Exp_int(Str2Int(sx), Exp_int(2, n-1)) % Str2Int(sz);
    
    var temp_squared := IntToString(Str2Int(temp) * Str2Int(temp));
    var q, r := DivMod(temp_squared, sz);
    res := r;
    
    calc {
      Str2Int(res);
      == (Str2Int(temp) * Str2Int(temp)) % Str2Int(sz);
      == Exp_int(Str2Int(temp), 2) % Str2Int(sz);
      == Exp_int(Exp_int(Str2Int(sx), Exp_int(2, n-1)) % Str2Int(sz), 2) % Str2Int(sz);
      == { ModExpLemma(Exp_int(Str2Int(sx), Exp_int(2, n-1)), 2, Str2Int(sz)); }
      Exp_int(Exp_int(Str2Int(sx), Exp_int(2, n-1)), 2) % Str2Int(sz);
      == { ExpPow2Lemma(Str2Int(sx), n); }
      Exp_int(Str2Int(sx), Exp_int(2, n)) % Str2Int(sz);
      == Exp_int(Str2Int(sx), Str2Int(sy)) % Str2Int(sz);
    }
  }
}
// </vc-code>

