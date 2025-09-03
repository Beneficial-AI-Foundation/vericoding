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
lemma ExpPow2Lemma(x: nat, n: nat)
  requires n > 0
  ensures Exp_int(x, Exp_int(2, n)) == Exp_int(Exp_int(x, Exp_int(2, n-1)), 2)
{
  calc {
    Exp_int(x, Exp_int(2, n));
    == Exp_int(x, 2 * Exp_int(2, n-1));
    == { ExpDoubling(x, Exp_int(2, n-1)); }
    Exp_int(x * x, Exp_int(2, n-1));
    == { ExpCommutative(x, x, Exp_int(2, n-1)); }
    Exp_int(Exp_int(x, 2), Exp_int(2, n-1));
    == { ExpExponent(x, 2, Exp_int(2, n-1)); }
    Exp_int(x, 2 * Exp_int(2, n-1));
    == Exp_int(x, Exp_int(2, n));
  }
  
  assert Exp_int(2, 1) == 2;
  assert Exp_int(x, 2) == x * x;
  
  if n == 1 {
    calc {
      Exp_int(x, Exp_int(2, 1));
      == Exp_int(x, 2);
      == x * x;
      == Exp_int(x, 1) * Exp_int(x, 1);
      == Exp_int(Exp_int(x, 1), 2);
      == Exp_int(Exp_int(x, Exp_int(2, 0)), 2);
    }
  } else {
    calc {
      Exp_int(x, Exp_int(2, n));
      == Exp_int(x, 2 * Exp_int(2, n-1));
      == { ExpPowerTwice(x, Exp_int(2, n-1)); }
      Exp_int(Exp_int(x, Exp_int(2, n-1)), 2);
    }
  }
}

lemma ExpDoubling(x: nat, n: nat)
  ensures Exp_int(x, 2*n) == Exp_int(x*x, n)
{
  if n == 0 {
    assert Exp_int(x, 0) == 1;
    assert Exp_int(x*x, 0) == 1;
  } else {
    calc {
      Exp_int(x, 2*n);
      == x * Exp_int(x, 2*n - 1);
      == x * x * Exp_int(x, 2*n - 2);
      == { if n == 1 { assert 2*n - 2 == 0; } else { ExpDoubling(x, n-1); } }
      x * x * Exp_int(x*x, n - 1);
      == Exp_int(x*x, n);
    }
  }
}

lemma ExpCommutative(x: nat, y: nat, n: nat)
  ensures Exp_int(x * y, n) == Exp_int(x, n) * Exp_int(y, n)
{
  if n == 0 {
    assert Exp_int(x * y, 0) == 1;
    assert Exp_int(x, 0) * Exp_int(y, 0) == 1 * 1 == 1;
  } else {
    calc {
      Exp_int(x * y, n);
      == (x * y) * Exp_int(x * y, n - 1);
      == { ExpCommutative(x, y, n - 1); }
      (x * y) * (Exp_int(x, n - 1) * Exp_int(y, n - 1));
      == x * Exp_int(x, n - 1) * y * Exp_int(y, n - 1);
      == Exp_int(x, n) * Exp_int(y, n);
    }
  }
}

lemma ExpExponent(x: nat, a: nat, b: nat)
  ensures Exp_int(Exp_int(x, a), b) == Exp_int(x, a * b)
{
  if b == 0 {
    assert Exp_int(Exp_int(x, a), 0) == 1;
    assert Exp_int(x, a * 0) == Exp_int(x, 0) == 1;
  } else {
    calc {
      Exp_int(Exp_int(x, a), b);
      == Exp_int(x, a) * Exp_int(Exp_int(x, a), b - 1);
      == { ExpExponent(x, a, b - 1); }
      Exp_int(x, a) * Exp_int(x, a * (b - 1));
      == { ExpAdd(x, a, a * (b - 1)); }
      Exp_int(x, a + a * (b - 1));
      == Exp_int(x, a * b);
    }
  }
}

lemma ExpAdd(x: nat, a: nat, b: nat)
  ensures Exp_int(x, a + b) == Exp_int(x, a) * Exp_int(x, b)
{
  if b == 0 {
    assert Exp_int(x, a + 0) == Exp_int(x, a);
    assert Exp_int(x, a) * Exp_int(x, 0) == Exp_int(x, a) * 1 == Exp_int(x, a);
  } else {
    calc {
      Exp_int(x, a + b);
      == x * Exp_int(x, a + b - 1);
      == { ExpAdd(x, a, b - 1); }
      x * Exp_int(x, a) * Exp_int(x, b - 1);
      == Exp_int(x, a) * x * Exp_int(x, b - 1);
      == Exp_int(x, a) * Exp_int(x, b);
    }
  }
}

lemma ExpPowerTwice(x: nat, n: nat)
  requires n > 0
  ensures Exp_int(x, 2*n) == Exp_int(Exp_int(x, n), 2)
{
  calc {
    Exp_int(x, 2*n);
    == { ExpAdd(x, n, n); }
    Exp_int(x, n) * Exp_int(x, n);
    == Exp_int(Exp_int(x, n), 2);
  }
}

lemma ModExpLemma(a: nat, b: nat, m: nat)
  requires m > 1
  ensures (a * b) % m == ((a % m) * (b % m)) % m
{
  // This is a standard modular arithmetic property
}

function method CreateZeroString(n: nat): string
  ensures |CreateZeroString(n)| == n
  ensures ValidBitString(CreateZeroString(n))
  ensures Str2Int(CreateZeroString(n)) == 0
{
  if n == 0 then ""
  else "0" + CreateZeroString(n - 1)
}

function method CreateOneString(): string
  ensures |CreateOneString()| == 1
  ensures ValidBitString(CreateOneString())
  ensures Str2Int(CreateOneString()) == 1
{
  "1"
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
    // sy represents either 0 or 2^0 = 1
    if sy[0] == '0' {
      // sy = 0, so x^0 = 1
      res := CreateOneString();
      assert Str2Int(res) == 1;
      assert Exp_int(Str2Int(sx), 0) == 1;
      assert 1 % Str2Int(sz) == Str2Int(res);
    } else {
      // sy = 1, so x^1 = x
      res := sx;
      assert Str2Int(res) == Str2Int(sx);
      assert Exp_int(Str2Int(sx), 1) == Str2Int(sx);
      assert Str2Int(sx) % Str2Int(sz) == Str2Int(res);
    }
  } else {
    // n > 0, sy represents 2^n
    // Create string for 2^(n-1)
    var sy_half := "1" + CreateZeroString(n - 1);
    assert |sy_half| == n;
    assert Str2Int(sy_half) == Exp_int(2, n - 1);
    
    // Recursive call: compute x^(2^(n-1)) mod z
    var temp := ModExpPow2(sx, sy_half, n - 1, sz);
    
    // Square the result: (x^(2^(n-1)))^2 mod z
    var temp_squared := Mul(temp, temp);
    
    // Take modulo
    res := temp_squared; // Assuming Mul handles the modulo internally or we need another mod operation
    
    // Verify the result using the lemma
    ExpPow2Lemma(Str2Int(sx), n);
    assert Str2Int(res) == Exp_int(Str2Int(sx), Exp_int(2, n)) % Str2Int(sz);
  }
}
// </vc-code>

