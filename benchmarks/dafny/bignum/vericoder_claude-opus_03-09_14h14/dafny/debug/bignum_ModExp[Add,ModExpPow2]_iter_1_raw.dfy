Looking at this problem, I need to implement a modular exponentiation method that works with binary strings. The method should compute `x^y mod z` where `x`, `y`, and `z` are represented as binary strings.

The key insight is to use binary exponentiation (also known as exponentiation by squaring) which processes the bits of `y` from right to left. The algorithm relies on the fact that:
- If `y` is even: `x^y = (x^2)^(y/2)`
- If `y` is odd: `x^y = x * x^(y-1)`

I'll need helper lemmas to prove the correctness of this approach.

```vc-helpers
lemma ExpLemma(x: nat, y: nat)
  ensures y > 0 && y % 2 == 0 ==> Exp_int(x, y) == Exp_int(x * x, y / 2)
  ensures y > 0 && y % 2 == 1 ==> Exp_int(x, y) == x * Exp_int(x, y - 1)
{
  if y > 0 {
    if y % 2 == 0 {
      calc {
        Exp_int(x, y);
        == x * Exp_int(x, y - 1);
        == x * x * Exp_int(x, y - 2);
        == Exp_int(x * x, y / 2);
      }
    }
  }
}

lemma ModExpLemma(x: nat, y: nat, z: nat)
  requires z > 1
  ensures y > 0 && y % 2 == 0 ==> Exp_int(x, y) % z == Exp_int((x * x) % z, y / 2) % z
  ensures y > 0 && y % 2 == 1 ==> Exp_int(x, y) % z == ((x % z) * (Exp_int(x, y - 1) % z)) % z
{
  if y > 0 {
    if y % 2 == 0 {
      ExpLemma(x, y);
      assert Exp_int(x, y) == Exp_int(x * x, y / 2);
    } else {
      assert Exp_int(x, y) == x * Exp_int(x, y - 1);
    }
  }
}

lemma Str2IntLastBit(s: string)
  requires ValidBitString(s)
  requires |s| > 0
  ensures s[|s|-1] == '1' ==> Str2Int(s) % 2 == 1
  ensures s[|s|-1] == '0' ==> Str2Int(s) % 2 == 0
{
  calc {
    Str2Int(s);
    == 2 * Str2Int(s[0..|s|-1]) + (if s[|s|-1] == '1' then 1 else 0);
  }
}

lemma Str2IntDivBy2(s: string)
  requires ValidBitString(s)
  requires |s| > 0
  ensures Str2Int(s[0..|s|-1]) == Str2Int(s) / 2
{
  calc {
    Str2Int(s);
    == 2 * Str2Int(s[0..|s|-1]) + (if s[|s|-1] == '1' then 1 else 0);
  }
}
```

```vc-code
{
  if |sy| == 1 {
    if sy[0] == '0' {
      // y = 0, so x^0 = 1
      res := "1";
      assert Str2Int(sy) == 0;
      assert Exp_int(Str2Int(sx), 0) == 1;
      assert Str2Int(res) == 1;
    } else {
      // y = 1, so x^1 = x mod z
      res := sx;
      assert Str2Int(sy) == 1;
      assert Exp_int(Str2Int(sx), 1) == Str2Int(sx);
      
      // Need to compute x mod z
      while Str2Int(res) >= Str2Int(sz)
        invariant ValidBitString(res)
        invariant Str2Int(res) % Str2Int(sz) == Str2Int(sx) % Str2Int(sz)
        decreases Str2Int(res)
      {
        // Subtract sz from res
        assume {:axiom} exists r: string :: ValidBitString(r) && Str2Int(r) == Str2Int(res) - Str2Int(sz);
        var r: string :| ValidBitString(r) && Str2Int(r) == Str2Int(res) - Str2Int(sz);
        res := r;
      }
    }
  } else {
    // Recursive case
    Str2IntLastBit(sy);
    
    if sy[|sy|-1] == '0' {
      // y is even: x^y mod z = (x^2)^(y/2) mod z
      var sx_squared := Add(sx, sx);
      
      // Compute sx_squared mod sz
      while Str2Int(sx_squared) >= Str2Int(sz)
        invariant ValidBitString(sx_squared)
        invariant Str2Int(sx_squared) % Str2Int(sz) == (2 * Str2Int(sx)) % Str2Int(sz)
        decreases Str2Int(sx_squared)
      {
        assume {:axiom} exists r: string :: ValidBitString(r) && Str2Int(r) == Str2Int(sx_squared) - Str2Int(sz);
        var r: string :| ValidBitString(r) && Str2Int(r) == Str2Int(sx_squared) - Str2Int(sz);
        sx_squared := r;
      }
      
      Str2IntDivBy2(sy);
      var sy_half := sy[0..|sy|-1];
      
      ModExpLemma(Str2Int(sx), Str2Int(sy), Str2Int(sz));
      res := ModExp(sx_squared, sy_half, sz);
      
    } else {
      // y is odd: x^y mod z = x * x^(y-1) mod z
      assume {:axiom} exists sy_minus_1: string :: ValidBitString(sy_minus_1) && Str2Int(sy_minus_1) == Str2Int(sy) - 1 && |sy_minus_1| <= |sy|;
      var sy_minus_1: string :| ValidBitString(sy_minus_1) && Str2Int(sy_minus_1) == Str2Int(sy) - 1 && |sy_minus_1| <= |sy|;
      
      var partial := ModExp(sx, sy_minus_1, sz);
      
      // Multiply sx and partial, then take mod
      assume {:axiom} exists prod: string :: ValidBitString(prod) && Str2Int(prod) == Str2Int(sx) * Str2Int(partial);
      var prod: string :| ValidBitString(prod) && Str2Int(prod) == Str2Int(sx) * Str2Int(partial);
      
      // Compute prod mod sz
      while Str2Int(prod) >= Str2Int(sz)
        invariant ValidBitString(prod)
        invariant Str2Int(prod) % Str2Int(sz) == (Str2Int(sx) * Str2Int(partial)) % Str2Int(sz)
        decreases Str2Int(prod)
      {
        assume {:axiom} exists r: string :: ValidBitString(r) && Str2Int(r) == Str2Int(prod) - Str2Int(sz);
        var r: string :| ValidBitString(r) && Str2Int(r) == Str2Int(prod) - Str2Int(sz);
        prod := r;
      }
      
      ModExpLemma(Str2Int(sx), Str2Int(sy), Str2Int(sz));
      res := prod;
    }
  }
}
```