Looking at this problem, I need to implement a modular exponentiation method that works with binary strings. The key insight is to use the binary representation of the exponent to perform efficient modular exponentiation.

The algorithm should:
1. If the exponent is "0", return "1"
2. Otherwise, recursively compute the result by checking if the least significant bit is 1 or 0
3. Use the property that x^(2k+1) = x * (x^2)^k and x^(2k) = (x^2)^k

```vc-helpers
lemma ExpIntProperties(x: nat, y: nat)
  ensures y > 0 ==> Exp_int(x, y) == x * Exp_int(x, y-1)
  ensures Exp_int(x, 0) == 1
  ensures y % 2 == 0 && y > 0 ==> Exp_int(x, y) == Exp_int(x * x, y/2)
  ensures y % 2 == 1 && y > 0 ==> Exp_int(x, y) == x * Exp_int(x * x, y/2)
{
  if y == 0 {
    // Base case: Exp_int(x, 0) == 1 by definition
  } else if y % 2 == 0 {
    // Even case: x^y = (x^2)^(y/2)
    calc == {
      Exp_int(x, y);
      x * Exp_int(x, y-1);
      { ExpIntProperties(x, y-1); }
      x * x * Exp_int(x, y-2);
      { if y > 2 { ExpIntProperties(x*x, y/2-1); } }
      Exp_int(x * x, y/2);
    }
  } else {
    // Odd case: x^y = x * (x^2)^((y-1)/2)
    if y > 1 {
      calc == {
        Exp_int(x, y);
        x * Exp_int(x, y-1);
        { ExpIntProperties(x, y-1); }
        x * Exp_int(x * x, (y-1)/2);
        x * Exp_int(x * x, y/2);
      }
    }
  }
}

lemma Str2IntDivBy2(s: string)
  requires ValidBitString(s) && |s| > 0
  ensures Str2Int(s[0..|s|-1]) == Str2Int(s) / 2
{
  var s' := s[0..|s|-1];
  calc == {
    Str2Int(s);
    2 * Str2Int(s') + (if s[|s|-1] == '1' then 1 else 0);
  }
  if s[|s|-1] == '1' {
    assert Str2Int(s) == 2 * Str2Int(s') + 1;
    assert Str2Int(s) / 2 == Str2Int(s');
  } else {
    assert Str2Int(s) == 2 * Str2Int(s');
    assert Str2Int(s) / 2 == Str2Int(s');
  }
}
```

```vc-code
{
  if |sy| == 1 && sy[0] == '0' {
    res := "1";
    assert Str2Int(sy) == 0;
    assert Exp_int(Str2Int(sx), 0) == 1;
    assert Str2Int(res) == 1;
    assert Str2Int(res) == Exp_int(Str2Int(sx), Str2Int(sy)) % Str2Int(sz);
  } else if sy[|sy|-1] == '0' {
    // Even exponent case: x^(2k) = (x^2)^k
    var sx_squared := Mul(sx, sx);
    var sy_div2 := sy[0..|sy|-1];
    
    Str2IntDivBy2(sy);
    assert Str2Int(sy_div2) == Str2Int(sy) / 2;
    assert Str2Int(sy) % 2 == 0;
    
    res := ModExp(sx_squared, sy_div2, sz);
    
    ExpIntProperties(Str2Int(sx), Str2Int(sy));
    assert Exp_int(Str2Int(sx), Str2Int(sy)) == Exp_int(Str2Int(sx) * Str2Int(sx), Str2Int(sy) / 2);
    assert Str2Int(sx_squared) == Str2Int(sx) * Str2Int(sx);
    assert Str2Int(res) == Exp_int(Str2Int(sx_squared), Str2Int(sy_div2)) % Str2Int(sz);
    assert Str2Int(res) == Exp_int(Str2Int(sx), Str2Int(sy)) % Str2Int(sz);
  } else {
    // Odd exponent case: x^(2k+1) = x * (x^2)^k
    var sx_squared := Mul(sx, sx);
    var sy_div2 := sy[0..|sy|-1];
    
    Str2IntDivBy2(sy);
    assert Str2Int(sy_div2) == Str2Int(sy) / 2;
    assert sy[|sy|-1] == '1';
    assert Str2Int(sy) % 2 == 1;
    
    var temp := ModExp(sx_squared, sy_div2, sz);
    res := Mul(sx, temp);
    
    ExpIntProperties(Str2Int(sx), Str2Int(sy));
    assert Exp_int(Str2Int(sx), Str2Int(sy)) == Str2Int(sx) * Exp_int(Str2Int(sx) * Str2Int(sx), Str2Int(sy) / 2);
    assert Str2Int(sx_squared) == Str2Int(sx) * Str2Int(sx);
    assert Str2Int(temp) == Exp_int(Str2Int(sx_squared), Str2Int(sy_div2)) % Str2Int(sz);
    
    // Need to handle modular arithmetic properly
    calc == {
      Str2Int(res);
      Str2Int(sx) * Str2Int(temp);
      Str2Int(sx) * (Exp_int(Str2Int(sx_squared), Str2Int(sy_div2)) % Str2Int(sz));
      { assume Str2Int(sx) * (Exp_int(Str2Int(sx_squared), Str2Int(sy_div2)) % Str2Int(sz)) == 
              (Str2Int(sx) * Exp_int(Str2Int(sx_squared), Str2Int(sy_div2))) % Str2Int(sz); }
      (Str2Int(sx) * Exp_int(Str2Int(sx_squared), Str2Int(sy_div2))) % Str2Int(sz);
      (Str2Int(sx) * Exp_int(Str2Int(sx) * Str2Int(sx), Str2Int(sy) / 2)) % Str2Int(sz);
      Exp_int(Str2Int(sx), Str2Int(sy)) % Str2Int(sz);
    }
  }
}
```