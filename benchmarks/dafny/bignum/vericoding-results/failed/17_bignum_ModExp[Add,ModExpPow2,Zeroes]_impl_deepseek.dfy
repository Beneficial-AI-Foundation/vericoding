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

method Zeros(n: nat) returns (s: string)
  ensures |s| == n
  ensures ValidBitString(s)
  ensures Str2Int(s) == 0
  ensures AllZero(s)
{
  assume{:axiom} false;
}

// <vc-helpers>
lemma Lemma_ExpZero(x: nat)
  ensures Exp_int(x, 0) == 1
{
}

lemma Lemma_ExpOne(x: nat)
  ensures Exp_int(x, 1) == x
{
}

lemma Lemma_ExpMult(x: nat, a: nat, b: nat)
  requires a >= 0 && b >= 0
  ensures Exp_int(x, a + b) == Exp_int(x, a) * Exp_int(x, b)
{
  if a == 0 {
    assert Exp_int(x, 0 + b) == Exp_int(x, b) == 1 * Exp_int(x, b);
  } else if b == 0 {
    assert Exp_int(x, a + 0) == Exp_int(x, a) == Exp_int(x, a) * 1;
  } else {
    calc {
      Exp_int(x, a + b);
      x * Exp_int(x, a + b - 1);
      { Lemma_ExpMult(x, a - 1, b); }
      x * (Exp_int(x, a - 1) * Exp_int(x, b));
      (x * Exp_int(x, a - 1)) * Exp_int(x, b);
      Exp_int(x, a) * Exp_int(x, b);
    }
  }
}

lemma Lemma_ExpSquare(x: nat, n: nat)
  ensures Exp_int(x, 2 * n) == Exp_int(Exp_int(x, n), 2)
{
  Lemma_ExpMult(x, n, n);
  assert Exp_int(x, n + n) == Exp_int(x, n) * Exp_int(x, n);
  assert Exp_int(Exp_int(x, n), 2) == Exp_int(x, n) * Exp_int(x, n);
}

lemma Lemma_ModExpPow2Zero(x: nat, n: nat, m: nat)
  requires m > 1
  ensures Exp_int(x, Exp_int(2, n)) % m == Exp_int(x % m, Exp_int(2, n)) % m
{
  if n == 0 {
    assert Exp_int(2, 0) == 1;
    assert Exp_int(x, 1) % m == (x % m) % m;
  } else {
    var prev := n - 1;
    Lemma_ModExpPow2Zero(x, prev, m);
    var half := Exp_int(2, prev);
    assert Exp_int(2, n) == 2 * half;
    Lemma_ExpSquare(x, half);
    assert Exp_int(x, Exp_int(2, n)) == Exp_int(x, 2 * half) == Exp_int(Exp_int(x, half), 2);
    assert Exp_int(Exp_int(x, half), 2) == Exp_int(x, half) * Exp_int(x, half);
    assert Exp_int(x % m, Exp_int(2, n)) == Exp_int(x % m, 2 * half) == Exp_int(Exp_int(x % m, half), 2);
    assert Exp_int(Exp_int(x % m, half), 2) == Exp_int(x % m, half) * Exp_int(x % m, half);
    assert Exp_int(x, half) % m == Exp_int(x % m, half) % m;
  }
}

lemma Lemma_ModMult(a: nat, b: nat, m: nat)
  requires m > 1
  ensures (a * b) % m == ((a % m) * (b % m)) % m
{
}

lemma Lemma_IfZeroChar(c: char)
  ensures (if c == '0' then 0 else 1) == 0 <==> c == '0'
{
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
    if sy[0] == '0' {
      var one_str := "1";
      res := one_str;
    } else {
      var x_val := Str2Int(sx);
      var m_val := Str2Int(sz);
      var mod_val := x_val % m_val;
      res := if mod_val == 0 then "0" else "1";
    }
  } else {
    var half_length := |sy| - 1;
    var half_sy := sy[0..half_length];
    
    var half_result := ModExp(sx, half_sy, sz);
    var half_val := Str2Int(half_result);
    var m_val := Str2Int(sz);
    
    var squared_val := half_val * half_val;
    var mod_squared := squared_val % m_val;
    
    if sy[|sy|-1] == '1' {
      var x_val := Str2Int(sx);
      var x_mod := x_val % m_val;
      var total := (mod_squared * x_mod) % m_val;
      res := if total == 0 then "0" else "1";
    } else {
      res := if mod_squared == 0 then "0" else "1";
    }
  }
}
// </vc-code>

