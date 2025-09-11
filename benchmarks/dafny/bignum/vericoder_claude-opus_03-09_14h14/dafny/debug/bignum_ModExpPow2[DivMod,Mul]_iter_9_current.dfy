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

method Mul(s1: string, s2: string) returns (res: string)
  requires ValidBitString(s1) && ValidBitString(s2)
  ensures ValidBitString(res)
  ensures Str2Int(res) == Str2Int(s1) * Str2Int(s2)
{
  assume{:axiom} false;
}

// <vc-helpers>
lemma ExpPow2Property(x: nat, n: nat)
  requires n > 0
  ensures Exp_int(x, Exp_int(2, n)) == Exp_int(Exp_int(x, Exp_int(2, n-1)), 2)
{
  calc {
    Exp_int(x, Exp_int(2, n));
    == Exp_int(x, 2 * Exp_int(2, n-1));
    == { ExpMultProperty(x, Exp_int(2, n-1), 2); }
    Exp_int(Exp_int(x, Exp_int(2, n-1)), 2);
  }
}

lemma ExpMultProperty(x: nat, a: nat, b: nat)
  ensures Exp_int(x, a * b) == Exp_int(Exp_int(x, a), b)
  decreases b
{
  if b == 0 {
    assert a * b == 0;
    assert Exp_int(x, 0) == 1;
    assert Exp_int(Exp_int(x, a), 0) == 1;
  } else if a == 0 {
    assert a * b == 0;
    assert Exp_int(x, 0) == 1;
    assert Exp_int(0, b) == 0;
    assert Exp_int(Exp_int(x, 0), b) == Exp_int(1, b) == 1;
  } else {
    assert a > 0 && b > 0;
    assert a * b > 0;
    calc {
      Exp_int(x, a * b);
      == { assert a * b - 1 == a * (b - 1) + (a - 1); }
      x * Exp_int(x, a * b - 1);
      == { ExpAddProperty(x, a * (b - 1), a - 1); }
      x * Exp_int(x, a * (b - 1)) * Exp_int(x, a - 1);
      == { ExpMultProperty(x, a, b - 1); }
      x * Exp_int(Exp_int(x, a), b - 1) * Exp_int(x, a - 1);
      == Exp_int(Exp_int(x, a), b - 1) * (x * Exp_int(x, a - 1));
      == Exp_int(Exp_int(x, a), b - 1) * Exp_int(x, a);
      == Exp_int(x, a) * Exp_int(Exp_int(x, a), b - 1);
      == Exp_int(Exp_int(x, a), b);
    }
  }
}

lemma ExpAddProperty(x: nat, a: nat, b: nat)
  ensures Exp_int(x, a + b) == Exp_int(x, a) * Exp_int(x, b)
  decreases b
{
  if b == 0 {
    assert Exp_int(x, a + 0) == Exp_int(x, a);
    assert Exp_int(x, b) == 1;
  } else {
    calc {
      Exp_int(x, a + b);
      == x * Exp_int(x, a + b - 1);
      == x * Exp_int(x, a + (b - 1));
      == { ExpAddProperty(x, a, b - 1); }
      x * Exp_int(x, a) * Exp_int(x, b - 1);
      == Exp_int(x, a) * (x * Exp_int(x, b - 1));
      == Exp_int(x, a) * Exp_int(x, b);
    }
  }
}

method MakePow2String(n: nat) returns (s: string)
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

function ZeroString(n: nat): string
  decreases n
{
  if n == 0 then "" else "0" + ZeroString(n - 1)
}

lemma ZeroStringProperties(n: nat)
  ensures ValidBitString(ZeroString(n))
  ensures |ZeroString(n)| == n
  ensures Str2Int(ZeroString(n)) == 0
  decreases n
{
  if n == 0 {
    assert ZeroString(0) == "";
    assert ValidBitString("");
    assert |""| == 0;
    assert Str2Int("") == 0;
  } else {
    ZeroStringProperties(n - 1);
    var zs := ZeroString(n);
    assert zs == "0" + ZeroString(n - 1);
    assert ValidBitString(ZeroString(n - 1));
    assert ValidBitString(zs);
    assert |zs| == 1 + |ZeroString(n - 1)| == 1 + (n - 1) == n;
    
    if n == 1 {
      assert ZeroString(0) == "";
      assert zs == "0";
      calc {
        Str2Int(zs);
        == Str2Int("0");
        == { assert |"0"| == 1; assert "0"[0] == '0'; }
        2 * Str2Int("0"[0..0]) + 0;
        == { assert "0"[0..0] == ""; }
        2 * Str2Int("") + 0;
        == 2 * 0 + 0;
        == 0;
      }
    } else {
      assert n >= 2;
      calc {
        Str2Int(zs);
        == Str2Int("0" + ZeroString(n - 1));
        == { assert |"0" + ZeroString(n - 1)| == n;
             assert ("0" + ZeroString(n - 1))[n-1] == ZeroString(n - 1)[n-2] == '0'; }
        2 * Str2Int(("0" + ZeroString(n - 1))[0..n-1]) + 0;
        == { assert ("0" + ZeroString(n - 1))[0..n-1] == "0" + ZeroString(n - 1)[0..n-2];
             assert |ZeroString(n - 1)| == n - 1;
             assert ZeroString(n - 1)[0..n-2] == ZeroString(n - 1)[0..|ZeroString(n - 1)|-1];
             assert ZeroString(n - 1)[0..|ZeroString(n - 1)|-1] == ZeroString(n - 2); }
        2 * Str2Int("0" + ZeroString(n - 2)) + 0;
        == { if n >= 2 { ZeroStringProperties(n - 2); } }
        2 * 0 + 0;
        == 0;
      }
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
  if sy == "0" {
    res := "1";
    return;
  }
  
  if n == 0 {
    assert sy == "1";
    assert Str2Int(sy) == 1;
    var _, rem := DivMod(sx, sz);
    res := rem;
    return;
  }
  
  assert n > 0;
  assert Str2Int(sy) == Exp_int(2, n);
  
  var pow_n_minus_1 := MakePow2String(n - 1);
  assert Str2Int(pow_n_minus_1) == Exp_int(2, n - 1);
  
  var temp := ModExpPow2(sx, pow_n_minus_1, n-1, sz);
  assert Str2Int(temp) == Exp_int(Str2Int(sx), Exp_int(2, n - 1)) % Str2Int(sz);
  
  var squared := Mul(temp, temp);
  var _, rem := DivMod(squared, sz);
  
  ExpPow2Property(Str2Int(sx), n);
  assert Exp_int(Str2Int(sx), Exp_int(2, n)) == Exp_int(Exp_int(Str2Int(sx), Exp_int(2, n-1)), 2);
  
  res := rem;
}
// </vc-code>

