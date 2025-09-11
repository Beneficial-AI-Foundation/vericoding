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
predicate AllZero(s: string)
{
  forall i | 0 <= i < |s| :: s[i] == '0'
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

method Zeros(n: nat) returns (s: string)
  ensures |s| == n
  ensures ValidBitString(s)
  ensures Str2Int(s) == 0
  ensures AllZero(s)
{
  assume{:axiom} false;
}

// <vc-helpers>
lemma Str2IntEven(s: string)
  requires ValidBitString(s)
  requires |s| > 0
  requires s[|s|-1] == '0'
  ensures Str2Int(s) == 2 * Str2Int(s[0..|s|-1])
{
  calc {
    Str2Int(s);
    == 2 * Str2Int(s[0..|s|-1]) + (if s[|s|-1] == '1' then 1 else 0);
    == 2 * Str2Int(s[0..|s|-1]) + 0;
    == 2 * Str2Int(s[0..|s|-1]);
  }
}

lemma Str2IntOdd(s: string)
  requires ValidBitString(s)
  requires |s| > 0
  requires s[|s|-1] == '1'
  ensures Str2Int(s) == 2 * Str2Int(s[0..|s|-1]) + 1
{
  calc {
    Str2Int(s);
    == 2 * Str2Int(s[0..|s|-1]) + (if s[|s|-1] == '1' then 1 else 0);
    == 2 * Str2Int(s[0..|s|-1]) + 1;
  }
}

lemma ExpIntEven(x: nat, y: nat)
  requires y > 0
  requires y % 2 == 0
  ensures Exp_int(x, y) == Exp_int(x * x, y / 2)
{
  if y == 2 {
    calc {
      Exp_int(x, 2);
      == x * Exp_int(x, 1);
      == x * x * Exp_int(x, 0);
      == x * x * 1;
      == x * x;
      == Exp_int(x * x, 1);
    }
  } else {
    calc {
      Exp_int(x, y);
      == x * Exp_int(x, y - 1);
      == x * x * Exp_int(x, y - 2);
      == { ExpIntEven(x, y - 2); }
      x * x * Exp_int(x * x, (y - 2) / 2);
      == Exp_int(x * x, y / 2);
    }
  }
}

lemma ExpIntOdd(x: nat, y: nat)
  requires y > 0
  requires y % 2 == 1
  ensures Exp_int(x, y) == x * Exp_int(x, y - 1)
{
  // This follows directly from the definition
}

lemma ValidBitStringPrefix(s: string)
  requires ValidBitString(s)
  requires |s| > 0
  ensures ValidBitString(s[0..|s|-1])
{
  forall i | 0 <= i < |s[0..|s|-1]| :: s[0..|s|-1][i] == '0' || s[0..|s|-1][i] == '1'
  {
    assert s[0..|s|-1][i] == s[i];
  }
}

lemma Str2IntZero(s: string)
  requires ValidBitString(s)
  requires AllZero(s)
  ensures Str2Int(s) == 0
{
  if |s| == 0 {
    // Base case
  } else {
    ValidBitStringPrefix(s);
    assert s[|s|-1] == '0';
    var prefix := s[0..|s|-1];
    assert forall i | 0 <= i < |prefix| :: prefix[i] == '0';
    Str2IntZero(prefix);
    calc {
      Str2Int(s);
      == 2 * Str2Int(prefix) + 0;
      == 2 * 0 + 0;
      == 0;
    }
  }
}

lemma Str2IntPositive(s: string)
  requires ValidBitString(s)
  requires |s| > 0
  requires !AllZero(s)
  ensures Str2Int(s) > 0
{
  if |s| == 1 {
    if s[0] == '1' {
      assert Str2Int(s) == 1;
    } else {
      assert s[0] == '0';
      assert AllZero(s);
      assert false;
    }
  } else {
    if s[|s|-1] == '1' {
      Str2IntOdd(s);
      assert Str2Int(s) == 2 * Str2Int(s[0..|s|-1]) + 1;
      assert Str2Int(s) >= 1;
    } else {
      ValidBitStringPrefix(s);
      var prefix := s[0..|s|-1];
      if !AllZero(prefix) {
        Str2IntPositive(prefix);
        Str2IntEven(s);
        assert Str2Int(s) == 2 * Str2Int(prefix);
        assert Str2Int(prefix) > 0;
        assert Str2Int(s) > 0;
      } else {
        assert forall i | 0 <= i < |prefix| :: prefix[i] == '0';
        assert s[|s|-1] == '0';
        assert forall i | 0 <= i < |s| :: s[i] == '0';
        assert AllZero(s);
        assert false;
      }
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
  var zeros := Zeros(|sy|);
  if sy == zeros {
    Str2IntZero(sy);
    assert Str2Int(sy) == 0;
    assert Exp_int(Str2Int(sx), 0) == 1;
    res := "1";
    assert Str2Int(res) == 1;
    assert Str2Int(res) == Exp_int(Str2Int(sx), Str2Int(sy)) % Str2Int(sz);
  } else {
    assert !AllZero(sy);
    Str2IntPositive(sy);
    assert Str2Int(sy) > 0;
    
    ValidBitStringPrefix(sy);
    if sy[|sy|-1] == '0' {
      Str2IntEven(sy);
      assert Str2Int(sy) % 2 == 0;
      var sx_squared := Mul(sx, sx);
      var sy_half := sy[0..|sy|-1];
      ExpIntEven(Str2Int(sx), Str2Int(sy));
      assert Exp_int(Str2Int(sx), Str2Int(sy)) == Exp_int(Str2Int(sx) * Str2Int(sx), Str2Int(sy) / 2);
      assert Str2Int(sx_squared) == Str2Int(sx) * Str2Int(sx);
      assert Str2Int(sy_half) == Str2Int(sy) / 2;
      res := ModExp(sx_squared, sy_half, sz);
    } else {
      Str2IntOdd(sy);
      assert Str2Int(sy) % 2 == 1;
      var sy_minus_one := sy[0..|sy|-1];
      var temp := ModExp(sx, sy_minus_one, sz);
      var sx_times_temp := Mul(sx, temp);
      ExpIntOdd(Str2Int(sx), Str2Int(sy));
      assert Exp_int(Str2Int(sx), Str2Int(sy)) == Str2Int(sx) * Exp_int(Str2Int(sx), Str2Int(sy) - 1);
      assert Str2Int(sy_minus_one) == (Str2Int(sy) - 1) / 2;
      assert Str2Int(temp) == Exp_int(Str2Int(sx), (Str2Int(sy) - 1) / 2) % Str2Int(sz);
      
      var recursive_call := ModExp(sx, sy_minus_one, sz);
      var recursive_squared := Mul(recursive_call, recursive_call);
      var result := Mul(sx, recursive_squared);
      res := result;
    }
  }
}
// </vc-code>

