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

method ModExpPow2(sx: string, sy: string, n: nat, sz: string) returns (res: string)
  requires ValidBitString(sx) && ValidBitString(sy) &&  ValidBitString(sz)
  // sy is power of 2 or zero
  requires Str2Int(sy) == Exp_int(2,n) || Str2Int(sy) == 0
  requires |sy| == n+1
  requires Str2Int(sz) > 1
  ensures ValidBitString(res)
  ensures Str2Int(res) == Exp_int(Str2Int(sx), Str2Int(sy)) % Str2Int(sz)
  decreases n
{
  assume{:axiom} false;
}

// <vc-helpers>
lemma ExpZero(x: nat)
  ensures Exp_int(x, 0) == 1
{
}

lemma ExpOne(x: nat)
  ensures Exp_int(x, 1) == x
{
}

lemma ExpEven(x: nat, y: nat)
  requires y > 0 && y % 2 == 0
  ensures Exp_int(x, y) == Exp_int(x * x, y / 2)
{
  if y == 2 {
    calc {
      Exp_int(x, 2);
      == x * Exp_int(x, 1);
      == x * (x * Exp_int(x, 0));
      == x * x * 1;
      == x * x;
      == Exp_int(x * x, 1);
    }
  } else {
    var half := y / 2;
    assert half > 0 && half % 2 == 0 by {
      assert y > 2;
      assert y % 2 == 0;
    }
    calc {
      Exp_int(x, y);
      == x * Exp_int(x, y - 1);
      == x * x * Exp_int(x, y - 2);
      == { ExpEven(x, y - 2); }
      x * x * Exp_int(x * x, (y - 2) / 2);
      == Exp_int(x * x, y / 2);
    }
  }
}

lemma ExpOdd(x: nat, y: nat)
  requires y > 0 && y % 2 == 1
  ensures Exp_int(x, y) == x * Exp_int(x, y - 1)
{
}

lemma ModMulLemma(a: nat, b: nat, m: nat)
  requires m > 0
  ensures ((a % m) * (b % m)) % m == (a * b) % m
{
}

lemma ExpDouble(x: nat, y: nat)
  ensures Exp_int(x, 2*y) == Exp_int(x, y) * Exp_int(x, y)
  decreases y
{
  if y == 0 {
    assert Exp_int(x, 0) == 1;
  } else {
    calc {
      Exp_int(x, 2*y);
      == x * Exp_int(x, 2*y - 1);
      == x * x * Exp_int(x, 2*y - 2);
      == { ExpDouble(x, y-1); }
      x * x * Exp_int(x, y-1) * Exp_int(x, y-1);
      == (x * Exp_int(x, y-1)) * (x * Exp_int(x, y-1));
      == Exp_int(x, y) * Exp_int(x, y);
    }
  }
}

function Str2Int_compiled(s: string): nat
  requires ValidBitString(s)
  decreases s
{
  if |s| == 0 then 0 else (2 * Str2Int_compiled(s[0..|s|-1]) + (if s[|s|-1] == '1' then 1 else 0))
}

lemma Str2IntEquiv(s: string)
  requires ValidBitString(s)
  ensures Str2Int(s) == Str2Int_compiled(s)
{
  if |s| == 0 {
  } else {
    Str2IntEquiv(s[0..|s|-1]);
  }
}

method IntToStr(n: nat) returns (s: string)
  ensures ValidBitString(s)
  ensures Str2Int(s) == n
{
  if n == 0 {
    s := "0";
    assert Str2Int(s) == 0;
  } else {
    var temp := n;
    s := "";
    assert Str2Int(s) == 0;
    while temp > 0
      invariant ValidBitString(s)
      invariant 0 <= temp
      invariant n == temp * Exp_int(2, |s|) + Str2Int(s)
      decreases temp
    {
      var oldS := s;
      var oldTemp := temp;
      if temp % 2 == 0 {
        s := "0" + s;
        assert s[|s|-1] == '0';
        assert Str2Int(s) == 2 * Str2Int(oldS) + 0;
      } else {
        s := "1" + s;
        assert s[|s|-1] == '1';
        assert Str2Int(s) == 2 * Str2Int(oldS) + 1;
      }
      temp := temp / 2;
      assert |s| == |oldS| + 1;
      assert Exp_int(2, |s|) == 2 * Exp_int(2, |oldS|);
      assert oldTemp == 2 * temp + (if oldTemp % 2 == 0 then 0 else 1);
    }
    assert temp == 0;
    assert n == 0 * Exp_int(2, |s|) + Str2Int(s);
  }
}

lemma AllZerosImpliesZero(s: string)
  requires ValidBitString(s)
  requires forall j | 0 <= j < |s| :: s[j] == '0'
  ensures Str2Int(s) == 0
  decreases |s|
{
  if |s| == 0 {
  } else {
    assert s[|s|-1] == '0';
    AllZerosImpliesZero(s[0..|s|-1]);
    assert Str2Int(s) == 2 * Str2Int(s[0..|s|-1]) + 0;
  }
}

lemma NotAllZerosImpliesNonZero(s: string)
  requires ValidBitString(s)
  requires exists j | 0 <= j < |s| :: s[j] == '1'
  ensures Str2Int(s) > 0
  decreases |s|
{
  if |s| == 0 {
    assert false;
  } else if s[|s|-1] == '1' {
    assert Str2Int(s) == 2 * Str2Int(s[0..|s|-1]) + 1;
    assert Str2Int(s) >= 1;
  } else {
    assert exists j | 0 <= j < |s|-1 :: s[0..|s|-1][j] == '1';
    NotAllZerosImpliesNonZero(s[0..|s|-1]);
    assert Str2Int(s[0..|s|-1]) > 0;
    assert Str2Int(s) == 2 * Str2Int(s[0..|s|-1]) + 0;
    assert Str2Int(s) > 0;
  }
}

method IsZero(s: string) returns (b: bool)
  requires ValidBitString(s)
  ensures b == (Str2Int(s) == 0)
{
  b := true;
  for i := 0 to |s|
    invariant b == (forall j | 0 <= j < i :: s[j] == '0')
    invariant b ==> Str2Int(s[0..i]) == 0
  {
    if s[i] != '0' {
      b := false;
      break;
    }
  }
  
  if b {
    assert forall j | 0 <= j < |s| :: s[j] == '0';
    AllZerosImpliesZero(s);
  } else {
    assert exists j | 0 <= j < |s| :: s[j] == '1';
    NotAllZerosImpliesNonZero(s);
  }
}

method ModMul(sx: string, sy: string, sz: string) returns (res: string)
  requires ValidBitString(sx) && ValidBitString(sy) && ValidBitString(sz)
  requires Str2Int(sz) > 0
  ensures ValidBitString(res)
  ensures Str2Int(res) == (Str2Int(sx) * Str2Int(sy)) % Str2Int(sz)
{
  Str2IntEquiv(sx);
  Str2IntEquiv(sy);
  Str2IntEquiv(sz);
  var product := Str2Int_compiled(sx) * Str2Int_compiled(sy);
  var modValue := Str2Int_compiled(sz);
  res := IntToStr(product % modValue);
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
  var isZero := IsZero(sy);
  if isZero {
    ExpZero(Str2Int(sx));
    assert Exp_int(Str2Int(sx), 0) == 1;
    assert Exp_int(Str2Int(sx), Str2Int(sy)) == 1;
    Str2IntEquiv(sz);
    var modValue := Str2Int_compiled(sz);
    res := IntToStr(1 % modValue);
    assert Str2Int(res) == 1 % Str2Int(sz);
    return;
  }
  
  if |sy| == 1 && sy[0] == '1' {
    assert sy == "1";
    assert Str2Int(sy) == 1;
    ExpOne(Str2Int(sx));
    assert Exp_int(Str2Int(sx), 1) == Str2Int(sx);
    Str2IntEquiv(sx);
    Str2IntEquiv(sz);
    var xVal := Str2Int_compiled(sx);
    var modValue := Str2Int_compiled(sz);
    res := IntToStr(xVal % modValue);
    assert Str2Int(res) == Str2Int(sx) % Str2Int(sz);
    return;
  }
  
  var lastBit := sy[|sy| - 1];
  var syDiv2 := sy[0..|sy|-1];
  assert ValidBitString(syDiv2);
  assert |syDiv2| < |sy|;
  
  if lastBit == '0' {
    assert Str2Int(sy) == 2 * Str2Int(syDiv2);
    assert Str2Int(sy) % 2 == 0;
    assert Str2Int(sy) > 0;
    ExpEven(Str2Int(sx), Str2Int(sy));
    assert Exp_int(Str2Int(sx), Str2Int(sy)) == Exp_int(Str2Int(sx) * Str2Int(sx), Str2Int(sy) / 2);
    assert Str2Int(sy) / 2 == Str2Int(syDiv2);
    var temp := ModExp(sx, syDiv2, sz);
    assert Str2Int(temp) == Exp_int(Str2Int(sx), Str2Int(syDiv2)) % Str2Int(sz);
    res := ModMul(temp, temp, sz);
    assert Str2Int(res) == (Str2Int(temp) * Str2Int(temp)) % Str2Int(sz);
    assert Str2Int(res) == ((Exp_int(Str2Int(sx), Str2Int(syDiv2)) % Str2Int(sz)) * (Exp_int(Str2Int(sx), Str2Int(syDiv2)) % Str2Int(sz))) % Str2Int(sz);
    ModMulLemma(Exp_int(Str2Int(sx), Str2Int(syDiv2)), Exp_int(Str2Int(sx), Str2Int(syDiv2)), Str2Int(sz));
    assert Str2Int(res) == (Exp_int(Str2Int(sx), Str2Int(syDiv2)) * Exp_int(Str2Int(sx), Str2Int(syDiv2))) % Str2Int(sz);
    assert Exp_int(Str2Int(sx), Str2Int(syDiv2)) * Exp_int(Str2Int(sx), Str2Int(syDiv2)) == Exp_int(Str2Int(sx) * Str2Int(sx), Str2Int(syDiv2));
    assert Str2Int(res) == Exp_int(Str2Int(sx) * Str2Int(sx), Str2Int(syDiv2)) % Str2Int(sz);
    assert Str2Int(res) == Exp_int(Str2Int(sx), Str2Int(sy)) % Str2Int(sz);
  } else {
    assert lastBit == '1';
    assert Str2Int(sy) == 2 * Str2Int(syDiv2) + 1;
    assert Str2Int(sy) % 2 == 1;
    assert Str2Int(sy) > 0;
    ExpOdd(Str2Int(sx), Str2Int(sy));
    assert Exp_int(Str2Int(sx), Str2Int(sy)) == Str2Int(sx) * Exp_int(Str2Int(sx), Str2Int(sy) - 1);
    assert Str2Int(sy) - 1 == 2 * Str2Int(syDiv2);
    ExpDouble(Str2Int(sx), Str2Int(syDiv2));
    var temp := ModExp(sx, syDiv2, sz);
    assert Str2Int(temp) == Exp_int(Str2Int(sx), Str2Int(syDiv2)) % Str2Int(sz);
    var tempSq := ModMul(temp, temp, sz);
    assert Str2Int(tempSq) == (Str2Int(temp) * Str2Int(temp)) % Str2Int(sz);
    ModMulLemma(Exp_int(Str2Int(sx), Str2Int(syDiv2)), Exp_int(Str2Int(sx), Str2Int(syDiv2)), Str2Int(sz));
    assert Str2Int(tempSq) == (Exp_int(Str2Int(sx), Str2Int(syDiv2)) * Exp_int(Str2Int(sx), Str2Int(syDiv2))) % Str2Int(sz);
    assert Str2Int(tempSq) == Exp_int(Str2Int(sx), 2 * Str2Int(syDiv2)) % Str2Int(sz);
    res := ModMul(tempSq, sx, sz);
    assert Str2Int(res) == (Str2Int(tempSq) * Str2Int(sx)) % Str2Int(sz);
    ModMulLemma(Exp_int(Str2Int(sx), 2 * Str2Int(syDiv2)), Str2Int(sx), Str2Int(sz));
    assert Str2Int(res) == (Exp_int(Str2Int(sx), 2 * Str2Int(syDiv2)) * Str2Int(sx)) % Str2Int(sz);
    assert Str2Int(res) == (Str2Int(sx) * Exp_int(Str2Int(sx), 2 * Str2Int(syDiv2))) % Str2Int(sz);
    assert Str2Int(res) == Exp_int(Str2Int(sx), Str2Int(sy)) % Str2Int(sz);
  }
}
// </vc-code>

