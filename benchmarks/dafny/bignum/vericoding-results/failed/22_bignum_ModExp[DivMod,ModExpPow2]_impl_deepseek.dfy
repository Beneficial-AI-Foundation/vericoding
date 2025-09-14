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
lemma LemmaExpMod(x: nat, y: nat, m: nat)
  requires m > 1
  ensures Exp_int(x, y) % m == (if y == 0 then 1 % m else (x * (Exp_int(x, y - 1) % m)) % m)
{
  if y == 0 {
    assert Exp_int(x, 0) == 1;
  } else {
    calc {
      Exp_int(x, y) % m;
      == { assert Exp_int(x, y) == x * Exp_int(x, y - 1); }
      (x * Exp_int(x, y - 1)) % m;
      == { LemmaModMul(x, Exp_int(x, y - 1), m); }
      ((x % m) * (Exp_int(x, y - 1) % m)) % m;
    }
  }
}

lemma LemmaExpZero(x: nat, y: nat)
  ensures Exp_int(x, y) == 0 <==> (x == 0 && y > 0)
{
  if x == 0 && y > 0 {
    var y' := y;
    while y' > 0
      decreases y'
      invariant y' <= y
      invariant Exp_int(0, y' + (y - y')) == 0
    {
      y' := y' - 1;
    }
  } else if y == 0 {
    assert Exp_int(x, 0) == 1;
  } else {
    assert x != 0;
    assert Exp_int(x, y) != 0;
  }
}

lemma LemmaExpSplit(x: nat, y1: nat, y2: nat)
  ensures Exp_int(x, y1 + y2) == Exp_int(x, y1) * Exp_int(x, y2)
{
  if y2 == 0 {
    assert Exp_int(x, y1 + 0) == Exp_int(x, y1);
    assert Exp_int(x, 0) == 1;
  } else {
    LemmaExpSplit(x, y1, y2 - 1);
    assert Exp_int(x, y1 + y2) == x * Exp_int(x, y1 + y2 - 1);
    assert Exp_int(x, y2) == x * Exp_int(x, y2 - 1);
  }
}

lemma LemmaModMul(a: nat, b: nat, m: nat)
  requires m > 0
  ensures (a * b) % m == ((a % m) * (b % m)) % m
{
  if m > 1 {
    calc {
      (a * b) % m;
      ==
      ((a % m + m * (a / m)) * (b % m + m * (b / m))) % m;
      ==
      ((a % m) * (b % m) + m * (a % m) * (b / m) + m * (a / m) * (b % m) + m * m * (a / m) * (b / m)) % m;
      == { 
        assert (m * (a % m) * (b / m)) % m == 0;
        assert (m * (a / m) * (b % m)) % m == 0;
        assert (m * m * (a / m) * (b / m)) % m == 0;
      }
      ((a % m) * (b % m)) % m;
    }
  } else {
    assert m == 1;
    assert (a * b) % m == 0;
    assert ((a % m) * (b % m)) % m == 0;
  }
}

function Int2Str(n: nat, len: nat): string
  requires len > 0 ==> n < Exp_int(2, len)
  ensures ValidBitString(Int2Str(n, len))
  ensures Str2Int(Int2Str(n, len)) == n
  ensures |Int2Str(n, len)| == len
  decreases len
{
  if len == 0 then "" else
    Int2Str(n / 2, len - 1) + (if n % 2 == 1 then "1" else "0")
}

lemma LemmaStr2IntInjective(s1: string, s2: string)
  requires ValidBitString(s1) && ValidBitString(s2)
  requires |s1| == |s2|
  requires Str2Int(s1) == Str2Int(s2)
  ensures s1 == s2
{
  if |s1| > 0 {
    var s1_prefix := s1[0..|s1|-1];
    var s2_prefix := s2[0..|s2|-1];
    assert Str2Int(s1) == 2 * Str2Int(s1_prefix) + (if s1[|s1|-1] == '1' then 1 else 0);
    assert Str2Int(s2) == 2 * Str2Int(s2_prefix) + (if s2[|s2|-1] == '1' then 1 else 0);
    
    assert Str2Int(s1_prefix) == Str2Int(s2_prefix);
    assert (if s1[|s1|-1] == '1' then 1 else 0) == (if s2[|s2|-1] == '1' then 1 else 0);
    
    LemmaStr2IntInjective(s1_prefix, s2_prefix);
  }
}

lemma LemmaExp2(n: nat)
  ensures n == 0 || Exp_int(2, n) == Str2Int(Int2Str(Exp_int(2, n), n+1))
  ensures |Int2Str(Exp_int(2, n), n+1)| == n+1
{
  if n == 0 {
    assert Exp_int(2, 0) == 1;
    assert Int2Str(1, 1) == "1";
    assert Str2Int("1") == 1;
  } else {
    LemmaExp2(n - 1);
    assert Exp_int(2, n) == 2 * Exp_int(2, n - 1);
    assert 2 * Exp_int(2, n - 1) == Exp_int(2, n);
    assert Exp_int(2, n) < Exp_int(2, n + 1);
  }
}

function Str2Int_nonghost(s: string): nat
  requires ValidBitString(s)
  decreases s
{
  if |s| == 0 then  0  else  (2 * Str2Int_nonghost(s[0..|s|-1]) + (if s[|s|-1] == '1' then 1 else 0))
}

lemma LemmaStr2IntEq(s: string)
  requires ValidBitString(s)
  ensures Str2Int(s) == Str2Int_nonghost(s)
{
  if |s| == 0 {
    assert Str2Int("") == 0;
    assert Str2Int_nonghost("") == 0;
  } else {
    LemmaStr2IntEq(s[0..|s|-1]);
    assert Str2Int(s) == 2 * Str2Int(s[0..|s|-1]) + (if s[|s|-1] == '1' then 1 else 0);
    assert Str2Int_nonghost(s) == 2 * Str2Int_nonghost(s[0..|s|-1]) + (if s[|s|-1] == '1' then 1 else 0);
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
  if |sy| == 1 {
    if sy == "0" {
      res := "1";
    } else {
      var mod_res_quotient, mod_res_remainder := DivMod(sx, sz);
      res := mod_res_remainder;
    }
  } else {
    var n := |sy| - 1;
    var half_sy := sy[0..n];
    var mod_half := ModExp(sx, half_sy, sz);
    
    var two_str := "10";
    var square := ModExp(mod_half, two_str, sz);
    
    if sy[n] == '1' {
      var mod_sx_quotient, mod_sx_remainder := DivMod(sx, sz);
      var multiply := ModExp(square, mod_sx_remainder, sz);
      res := multiply;
    } else {
      res := square;
    }
  }
}
// </vc-code>

