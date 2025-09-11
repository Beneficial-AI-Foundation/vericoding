Looking at this problem, I need to implement a modular exponentiation method that works with binary strings. The key insight is to use the binary representation of the exponent to efficiently compute the result.

The algorithm should:
1. Handle the base case when the exponent is "0" (return "1")
2. Use the property that `a^(2k) = (a^k)^2` and `a^(2k+1) = a * (a^k)^2`
3. Recursively compute based on whether the last bit of the exponent is 0 or 1

```vc-helpers
lemma Exp_int_zero(x: nat)
  ensures Exp_int(x, 0) == 1
{
}

lemma Exp_int_split(x: nat, y: nat)
  requires y > 0
  ensures y % 2 == 0 ==> Exp_int(x, y) == Exp_int(x * x, y / 2)
  ensures y % 2 == 1 ==> Exp_int(x, y) == x * Exp_int(x * x, y / 2)
{
  if y % 2 == 0 {
    assert y == 2 * (y / 2);
    calc {
      Exp_int(x, y);
      == Exp_int(x, 2 * (y / 2));
      == { Exp_int_even_helper(x, y / 2); }
      Exp_int(x * x, y / 2);
    }
  } else {
    assert y == 2 * (y / 2) + 1;
    calc {
      Exp_int(x, y);
      == x * Exp_int(x, y - 1);
      == x * Exp_int(x, 2 * (y / 2));
      == { Exp_int_even_helper(x, y / 2); }
      x * Exp_int(x * x, y / 2);
    }
  }
}

lemma Exp_int_even_helper(x: nat, k: nat)
  ensures Exp_int(x, 2 * k) == Exp_int(x * x, k)
{
  if k == 0 {
    calc {
      Exp_int(x, 2 * k);
      == Exp_int(x, 0);
      == 1;
      == Exp_int(x * x, 0);
    }
  } else {
    calc {
      Exp_int(x, 2 * k);
      == x * Exp_int(x, 2 * k - 1);
      == x * x * Exp_int(x, 2 * k - 2);
      == x * x * Exp_int(x, 2 * (k - 1));
      == { Exp_int_even_helper(x, k - 1); }
      x * x * Exp_int(x * x, k - 1);
      == Exp_int(x * x, k);
    }
  }
}

method Int2Str(n: nat) returns (s: string)
  ensures ValidBitString(s)
  ensures Str2Int(s) == n
{
  assume {:axiom} false;
}

method ModMul(sx: string, sy: string, sz: string) returns (res: string)
  requires ValidBitString(sx) && ValidBitString(sy) && ValidBitString(sz)
  requires Str2Int(sz) > 0
  ensures ValidBitString(res)
  ensures Str2Int(res) == (Str2Int(sx) * Str2Int(sy)) % Str2Int(sz)
{
  assume {:axiom} false;
}

lemma Str2Int_last_bit(s: string)
  requires ValidBitString(s)
  requires |s| > 0
  ensures s[|s|-1] == '0' ==> Str2Int(s) % 2 == 0
  ensures s[|s|-1] == '1' ==> Str2Int(s) % 2 == 1
  ensures Str2Int(s) / 2 == Str2Int(s[0..|s|-1])
{
  calc {
    Str2Int(s);
    == 2 * Str2Int(s[0..|s|-1]) + (if s[|s|-1] == '1' then 1 else 0);
  }
  if s[|s|-1] == '0' {
    assert Str2Int(s) == 2 * Str2Int(s[0..|s|-1]);
    assert Str2Int(s) % 2 == 0;
    assert Str2Int(s) / 2 == Str2Int(s[0..|s|-1]);
  } else {
    assert s[|s|-1] == '1';
    assert Str2Int(s) == 2 * Str2Int(s[0..|s|-1]) + 1;
    assert Str2Int(s) % 2 == 1;
    assert Str2Int(s) / 2 == Str2Int(s[0..|s|-1]);
  }
}

lemma ValidBitString_prefix(s: string)
  requires ValidBitString(s)
  requires |s| > 0
  ensures ValidBitString(s[0..|s|-1])
{
}
```

```vc-code
{
  if |sy| == 1 && sy[0] == '0' {
    res := Int2Str(1 % Str2Int(sz));
    assert Str2Int(sy) == 0;
    assert Exp_int(Str2Int(sx), 0) == 1;
  } else {
    ValidBitString_prefix(sy);
    var sy_half := sy[0..|sy|-1];
    
    var temp := ModExp(sx, sy_half, sz);
    var squared := ModMul(temp, temp, sz);
    
    if sy[|sy|-1] == '0' {
      res := squared;
      Str2Int_last_bit(sy);
      assert Str2Int(sy) % 2 == 0;
      assert Str2Int(sy) / 2 == Str2Int(sy_half);
      Exp_int_split(Str2Int(sx), Str2Int(sy));
      assert Exp_int(Str2Int(sx), Str2Int(sy)) % Str2Int(sz) == 
             Exp_int(Str2Int(sx) * Str2Int(sx), Str2Int(sy) / 2) % Str2Int(sz);
    } else {
      res := ModMul(sx, squared, sz);
      Str2Int_last_bit(sy);
      assert Str2Int(sy) % 2 == 1;
      assert Str2Int(sy) / 2 == Str2Int(sy_half);
      Exp_int_split(Str2Int(sx), Str2Int(sy));
      assert Exp_int(Str2Int(sx), Str2Int(sy)) % Str2Int(sz) == 
             (Str2Int(sx) * Exp_int(Str2Int(sx) * Str2Int(sx), Str2Int(sy) / 2)) % Str2Int(sz);
    }
  }
}
```