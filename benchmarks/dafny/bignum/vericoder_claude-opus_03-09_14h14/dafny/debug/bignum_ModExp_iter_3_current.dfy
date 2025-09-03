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

// <vc-helpers>
lemma Str2IntConcat0(s: string)
  requires ValidBitString(s)
  ensures ValidBitString("0" + s)
  ensures Str2Int("0" + s) == 2 * Str2Int(s)
{
  calc {
    Str2Int("0" + s);
    == 2 * Str2Int(("0" + s)[0..|"0" + s|-1]) + (if ("0" + s)[|"0" + s|-1] == '1' then 1 else 0);
    == 2 * Str2Int(s) + (if s[|s|-1] == '1' then 1 else 0);
    == 2 * Str2Int(s) + 0;
    == 2 * Str2Int(s);
  }
}

lemma Str2IntConcat1(s: string)
  requires ValidBitString(s)
  ensures ValidBitString("1" + s)
  ensures Str2Int("1" + s) == 2 * Str2Int(s) + 1
{
  if |s| == 0 {
    assert Str2Int("1") == 1;
  } else {
    calc {
      Str2Int("1" + s);
      == 2 * Str2Int(("1" + s)[0..|"1" + s|-1]) + (if ("1" + s)[|"1" + s|-1] == '1' then 1 else 0);
      == 2 * Str2Int("1" + s[0..|s|-1]) + (if s[|s|-1] == '1' then 1 else 0);
      == 2 * Str2Int("1" + s[0..|s|-1]) + (if s[|s|-1] == '1' then 1 else 0);
    }
  }
}

method Int2Str(n: nat) returns (s: string)
  ensures ValidBitString(s)
  ensures Str2Int(s) == n
{
  if n == 0 {
    s := "0";
  } else {
    var temp := n;
    s := "";
    while temp > 0
      invariant 0 <= temp <= n
      invariant ValidBitString(s)
      invariant n == temp * Exp_int(2, |s|) + Str2Int(s)
      decreases temp
    {
      var old_s := s;
      var old_temp := temp;
      
      if temp % 2 == 0 {
        s := "0" + s;
        Str2IntConcat0(old_s);
      } else {
        s := "1" + s;
        Str2IntConcat1(old_s);
      }
      temp := temp / 2;
      
      // Verify invariant maintenance
      assert |s| == |old_s| + 1;
      assert Exp_int(2, |s|) == 2 * Exp_int(2, |old_s|);
      
      if old_temp % 2 == 0 {
        calc {
          temp * Exp_int(2, |s|) + Str2Int(s);
          == (old_temp / 2) * (2 * Exp_int(2, |old_s|)) + 2 * Str2Int(old_s);
          == old_temp * Exp_int(2, |old_s|) + Str2Int(old_s);
          == n;
        }
      } else {
        calc {
          temp * Exp_int(2, |s|) + Str2Int(s);
          == (old_temp / 2) * (2 * Exp_int(2, |old_s|)) + (2 * Str2Int(old_s) + 1);
          == ((old_temp - 1) / 2) * (2 * Exp_int(2, |old_s|)) + (2 * Str2Int(old_s) + 1);
          == (old_temp - 1) * Exp_int(2, |old_s|) + 2 * Str2Int(old_s) + 1;
          == old_temp * Exp_int(2, |old_s|) + Str2Int(old_s);
          == n;
        }
      }
    }
    
    if |s| == 0 {
      s := "0";
    }
  }
}

method StrToInt(s: string) returns (n: nat)
  requires ValidBitString(s)
  ensures n == Str2Int(s)
{
  n := 0;
  var i := 0;
  while i < |s|
    invariant 0 <= i <= |s|
    invariant n == Str2Int(s[0..i])
  {
    var old_n := n;
    n := n * 2;
    if s[i] == '1' {
      n := n + 1;
    }
    
    // Help the verifier with the invariant
    assert s[0..i+1] == s[0..i] + [s[i]];
    assert Str2Int(s[0..i+1]) == 2 * Str2Int(s[0..i]) + (if s[i] == '1' then 1 else 0);
    
    i := i + 1;
  }
  assert s[0..|s|] == s;
}

method IsEven(s: string) returns (even: bool)
  requires ValidBitString(s)
  requires |s| > 0
  ensures even == (Str2Int(s) % 2 == 0)
{
  even := (s[|s|-1] == '0');
}

method DivBy2(s: string) returns (res: string)
  requires ValidBitString(s)
  requires |s| > 0
  ensures ValidBitString(res)
  ensures Str2Int(res) == Str2Int(s) / 2
{
  if |s| == 1 {
    res := "0";
  } else {
    res := s[0..|s|-1];
  }
}

method ModMult(sx: string, sy: string, sz: string) returns (res: string)
  requires ValidBitString(sx) && ValidBitString(sy) && ValidBitString(sz)
  requires Str2Int(sz) > 0
  ensures ValidBitString(res)
  ensures Str2Int(res) == (Str2Int(sx) * Str2Int(sy)) % Str2Int(sz)
{
  var x := StrToInt(sx);
  var y := StrToInt(sy);
  var z := StrToInt(sz);
  var prod := (x * y) % z;
  res := Int2Str(prod);
}

lemma ExpEvenPower(x: nat, y: nat)
  requires y > 0 && y % 2 == 0
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
    var half := y / 2;
    assert y == 2 * half;
    calc {
      Exp_int(x, y);
      == Exp_int(x, 2 * half);
      == { ExpDoubling(x, half); }
      Exp_int(x * x, half);
      == Exp_int(x * x, y / 2);
    }
  }
}

lemma ExpDoubling(x: nat, k: nat)
  ensures Exp_int(x, 2 * k) == Exp_int(x * x, k)
{
  if k == 0 {
    assert Exp_int(x, 0) == 1;
    assert Exp_int(x * x, 0) == 1;
  } else {
    calc {
      Exp_int(x, 2 * k);
      == x * Exp_int(x, 2 * k - 1);
      == x * x * Exp_int(x, 2 * k - 2);
      == x * x * Exp_int(x, 2 * (k - 1));
      == { ExpDoubling(x, k - 1); }
      x * x * Exp_int(x * x, k - 1);
      == (x * x) * Exp_int(x * x, k - 1);
      == Exp_int(x * x, k);
    }
  }
}

lemma ExpOddPower(x: nat, y: nat)
  requires y > 0 && y % 2 == 1
  ensures Exp_int(x, y) == x * Exp_int(x, y - 1)
{
}

lemma DivBy2Decreases(s: string)
  requires ValidBitString(s)
  requires |s| > 1
  ensures |s[0..|s|-1]| < |s|
{
  assert |s[0..|s|-1]| == |s| - 1;
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
  if |sy| == 1 && sy[0] == '0' {
    res := "1";
    assert Str2Int(sy) == 0;
    assert Exp_int(Str2Int(sx), 0) == 1;
    return;
  }
  
  var isEven := IsEven(sy);
  
  if isEven {
    var halfY := DivBy2(sy);
    
    if |sy| == 1 {
      // sy must be "0" since it's even and has length 1
      assert sy == "0";
      res := "1";
      return;
    }
    
    // Now we know |sy| > 1, so |halfY| >= 1
    assert |sy| > 1;
    DivBy2Decreases(sy);
    assert |halfY| == |sy| - 1;
    assert |halfY| < |sy|;
    assert |halfY| > 0;
    
    var temp := ModExp(sx, halfY, sz);
    
    assert Str2Int(sy) > 0;
    assert Str2Int(sy) % 2 == 0;
    ExpEvenPower(Str2Int(sx), Str2Int(sy));
    res := ModMult(temp, temp, sz);
  } else {
    if |sy| == 1 && sy[0] == '1' {
      var x := StrToInt(sx);
      var z := StrToInt(sz);
      var r := x % z;
      res := Int2Str(r);
      assert Str2Int(sy) == 1;
      assert Exp_int(Str2Int(sx), 1) == Str2Int(sx);
    } else {
      var sy_minus_1_int := StrToInt(sy);
      sy_minus_1_int := sy_minus_1_int - 1;
      var sy_minus_1 := Int2Str(sy_minus_1_int);
      
      assert Str2Int(sy_minus_1) == Str2Int(sy) - 1;
      assert Str2Int(sy) % 2 == 1;
      assert (Str2Int(sy) - 1) % 2 == 0;
      
      var halfY := DivBy2(sy_minus_1);
      assert Str2Int(halfY) == (Str2Int(sy) - 1) / 2;
      
      // Since sy is odd and > 1, sy >= 3, so sy-1 >= 2
      assert Str2Int(sy) >= 3;
      assert Str2Int(sy) - 1 >= 2;
      assert Str2Int(sy_minus_1) >= 2;
      
      // This means |sy_minus_1| >= 2 (since "10" represents 2 in binary)
      // Actually we need to be careful - sy_minus_1 could still be "1" if sy was "11" (3)
      // Let's check: if sy - 1 >= 2, then halfY >= 1
      assert Str2Int(halfY) >= 1;
      
      // This ensures |halfY| > 0
      if |halfY| == 0 {
        // This would mean Str2Int(halfY) == 0, contradiction
        assert false;
      }
      
      assert |halfY| > 0;
      assert |halfY| <= |sy_minus_1|;
      
      var temp := ModExp(sx, halfY, sz);
      var temp_squared := ModMult(temp, temp, sz);
      ExpOddPower(Str2Int(sx), Str2Int(sy));
      ExpEvenPower(Str2Int(sx), Str2Int(sy) - 1);
      res := ModMult(sx, temp_squared, sz);
    }
  }
}
// </vc-code>

