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

method Add(s1: string, s2: string) returns (res: string)
  requires ValidBitString(s1) && ValidBitString(s2)
  ensures ValidBitString(res)
  ensures Str2Int(res) == Str2Int(s1) + Str2Int(s2)
{
  assume{:axiom} false;
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
function Str2IntImpl(s: string): nat
  requires ValidBitString(s)
  decreases s
{
  if |s| == 0 then  0  else  (2 * Str2IntImpl(s[0..|s|-1]) + (if s[|s|-1] == '1' then 1 else 0))
}

lemma Str2IntImplEqualsGhost(s: string)
  requires ValidBitString(s)
  ensures Str2IntImpl(s) == Str2Int(s)
{
  if |s| == 0 {
  } else {
    Str2IntImplEqualsGhost(s[0..|s|-1]);
    calc {
      Str2IntImpl(s);
      2 * Str2IntImpl(s[0..|s|-1]) + (if s[|s|-1] == '1' then 1 else 0);
      2 * Str2Int(s[0..|s|-1]) + (if s[|s|-1] == '1' then 1 else 0);
      Str2Int(s);
    }
  }
}

function ModExp_Helper(x: nat, y: nat, m: nat): nat
  requires m > 1
  decreases y
{
  if y == 0 then 1 % m
  else 
    var temp := ModExp_Helper(x, y / 2, m);
    var temp2 := (temp * temp) % m;
    if y % 2 == 0 then temp2 else (temp2 * (x % m)) % m
}

function Int2Str(n: nat, m: nat): string
  decreases m
{
  if m == 0 then "" else Int2Str(n / 2, m - 1) + (if n % 2 == 1 then "1" else "0")
}

lemma Int2StrValidBitString(n: nat, m: nat)
  ensures ValidBitString(Int2Str(n, m))
{
  if m == 0 {
  } else {
    Int2StrValidBitString(n/2, m-1);
    var s := Int2Str(n/2, m-1);
    var c := if n%2==1 then "1" else "0";
    assert forall i | 0 <= i < |s| :: s[i] in ['0','1'];
    assert c[0] in ['0','1'];
  }
}

lemma Int2StrCorrect(n: nat, m: nat)
  requires n < Exp_int(2, m)
  ensures Str2Int(Int2Str(n, m)) == n
{
  Int2StrValidBitString(n, m);
  if m == 0 {
    calc {
      Str2Int(Int2Str(n, m));
      Str2Int("");
      0;
      n;
    }
  } else {
    Int2StrCorrect(n/2, m-1);
    calc {
      Str2Int(Int2Str(n, m));
      Str2Int(Int2Str(n/2, m-1) + (if n%2==1 then "1" else "0"));
      2 * Str2Int(Int2Str(n/2, m-1)) + (if n%2==1 then 1 else 0);
      2 * (n/2) + (n % 2);
      n;
    }
  }
}

lemma ModExp_Helper_Correct(x: nat, y: nat, m: nat)
  requires m > 1
  ensures ModExp_Helper(x, y, m) == Exp_int(x, y) % m
  decreases y
{
  if y == 0 {
    calc {
      ModExp_Helper(x, y, m);
      1 % m;
      Exp_int(x,0) % m;
    }
  } else {
    ModExp_Helper_Correct(x, y/2, m);
    calc {
      ModExp_Helper(x, y, m);
      { reveal ModExp_Helper(); }
      var temp := ModExp_Helper(x, y/2, m);
      var temp2 := (temp * temp) % m;
      if y % 2 == 0 then temp2 else (temp2 * (x % m)) % m;
      == 
      if y % 2 == 0 then (temp * temp) % m else (temp * temp * x) % m;
      { 
        assert temp == Exp_int(x, y/2) % m;
        assert (temp * temp) % m == (Exp_int(x, y/2) * Exp_int(x, y/2)) % m;
        assert (Exp_int(x, y/2) * Exp_int(x, y/2)) % m == Exp_int(x, 2*(y/2)) % m;
        if y % 2 == 0 {
          assert 2*(y/2) == y;
        } else {
          assert 2*(y/2) == y-1;
          assert (temp * temp * x) % m == (Exp_int(x, y-1) * x) % m;
          assert Exp_int(x, y-1) * x == Exp_int(x, y);
        }
      }
      Exp_int(x, y) % m;
    }
  }
}

lemma ModExp_Helper_Bounded(x: nat, y: nat, m: nat)
  requires m > 1
  ensures ModExp_Helper(x, y, m) < m
  decreases y
{
  if y == 0 {
    calc {
      ModExp_Helper(x, y, m);
      1 % m;
      <= m-1;
      < m;
    }
  } else {
    ModExp_Helper_Bounded(x, y/2, m);
    var temp := ModExp_Helper(x, y/2, m);
    var temp2 := (temp * temp) % m;
    assert temp2 < m;
    if y % 2 == 0 {
      assert ModExp_Helper(x, y, m) == temp2;
    } else {
      var x_mod := x % m;
      assert x_mod < m;
      var product := temp2 * x_mod;
      assert product < m * m;
      var result := product % m;
      assert result < m;
      assert ModExp_Helper(x, y, m) == result;
    }
  }
}

lemma Str2IntLessThanExp(s: string)
  requires ValidBitString(s)
  ensures Str2Int(s) < Exp_int(2, |s|)
{
  if |s| == 0 {
    calc {
      Str2Int(s);
      0;
      Exp_int(2,0) - 1;
      < Exp_int(2,0);
    }
  } else {
    Str2IntLessThanExp(s[0..|s|-1]);
    calc {
      Str2Int(s);
      2 * Str2Int(s[0..|s|-1]) + (if s[|s|-1]=='1' then 1 else 0);
      <= 2 * Str2Int(s[0..|s|-1]) + 1;
      < 2 * (Exp_int(2, |s|-1));
      == Exp_int(2, |s|);
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
  Str2IntImplEqualsGhost(sx);
  Str2IntImplEqualsGhost(sy);
  Str2IntImplEqualsGhost(sz);
  var x_int := Str2IntImpl(sx);
  var y_int := Str2IntImpl(sy);
  var z_int := Str2IntImpl(sz);
  var res_int := ModExp_Helper(x_int, y_int, z_int);
  var len := |sz|;
  Str2IntLessThanExp(sz);
  assert z_int < Exp_int(2, len);
  ModExp_Helper_Bounded(x_int, y_int, z_int);
  assert res_int < z_int;
  assert res_int < Exp_int(2, len);
  ModExp_Helper_Correct(x_int, y_int, z_int);
  Int2StrCorrect(res_int, len);
  Int2StrValidBitString(res_int, len);
  res := Int2Str(res_int, len);
}
// </vc-code>

