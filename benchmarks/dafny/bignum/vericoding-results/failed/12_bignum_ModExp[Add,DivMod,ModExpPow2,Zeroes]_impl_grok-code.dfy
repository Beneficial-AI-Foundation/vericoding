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

method Zeros(n: nat) returns (s: string)
  ensures |s| == n
  ensures ValidBitString(s)
  ensures Str2Int(s) == 0
  ensures AllZero(s)
{
  assume{:axiom} false;
}

// <vc-helpers>
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
  var sum_nat := Str2Int(s1) + Str2Int(s2);
  IntStrInverse(sum_nat);
  res := Int2Str(sum_nat);
}

method DivMod(dividend: string, divisor: string) returns (quotient: string, remainder: string)
  requires ValidBitString(dividend) && ValidBitString(divisor)
  requires Str2Int(divisor) > 0
  ensures ValidBitString(quotient) && ValidBitString(remainder)
  ensures Str2Int(quotient) == Str2Int(dividend) / Str2Int(divisor)
  ensures Str2Int(remainder) == Str2Int(dividend) % Str2Int(divisor)
{
  var d_nat := Str2Int(dividend);
  var v_nat := Str2Int(divisor);
  assert v_nat > 0;
  var q_nat := d_nat / v_nat;
  var r_nat := d_nat % v_nat;
  IntStrInverse(q_nat);
  IntStrInverse(r_nat);
  quotient := Int2Str(q_nat);
  remainder := Int2Str(r_nat);
}

method ModExpPow2(sx: string, sy: string, n: nat, sz: string) returns (res: string)
  requires ValidBitString(sx) && ValidBitString(sy) &&  ValidBitString(sz)
  requires Str2Int(sy) == Exp_int(2,n) || Str2Int(sy) == 0
  requires |sy| == n+1
  requires Str2Int(sz) > 1
  ensures ValidBitString(res)
  ensures Str2Int(res) == Exp_int(Str2Int(sx), Str2Int(sy)) % Str2Int(sz)
  decreases n
{
  if n == 0 {
    var x_nat := Str2Int(sx);
    var z_nat := Str2Int(sz);
    var r_nat := x_nat % z_nat;
    IntStrInverse(r_nat);
    res := Int2Str(r_nat);
  } else {
    var temp := ModExpPow2(sx, sy, n-1, sz);
    var t_nat := Str2Int(temp) * Str2Int(temp);
    var r_nat := t_nat % Str2Int(sz);
    IntStrInverse(r_nat);
    res := Int2Str(r_nat);
  }
}

method Zeros(n: nat) returns (s: string)
  ensures |s| == n
  ensures ValidBitString(s)
  ensures Str2Int(s) == 0
  ensures AllZero(s)
{
  s := "";
  var i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant |s| == i
    invariant ValidBitString(s)
    invariant Str2Int(s) == 0
    invariant AllZero(s)
  {
    s := s + "0";
    i := i + 1;
  }
}

function Int2Str(n: nat): string
{
  if n == 0 then "0" else Int2Str(n / 2) + (if n % 2 == 1 then "1" else "0")
}

lemma IntStrInverse(n: nat)
  ensures ValidBitString(Int2Str(n))
  ensures Str2Int(Int2Str(n)) == n
{
  if n != 0 {
    IntStrInverse(n / 2);
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
  ghost var x_nat := Str2Int(sx);
  ghost var z_nat := Str2Int(sz);
  ghost var y_nat := Str2Int(sy);
  if y_nat == 0 {
    var one_str := "1";
    var _, remainder := DivMod(one_str, sz);
    res := remainder;
    assert Str2Int(res) == 1 % z_nat;
  } else if |sy| == 1 && sy[0] == '1' {
    var r_nat := x_nat % z_nat;
    IntStrInverse(r_nat);
    res := Int2Str(r_nat);
    assert Str2Int(res) == Exp_int(x_nat, 1) % z_nat;
  } else {
    var dy: string := sy[0..|sy|-1];
    var d_nat := Str2Int(dy);
    var temp := ModExp(sx, dy, sz);
    assert Str2Int(temp) == Exp_int(x_nat, d_nat) % z_nat;
    var t_nat := Str2Int(temp) * Str2Int(temp);
    var r_nat := t_nat % z_nat;
    assert r_nat == Exp_int(x_nat, 2 * d_nat) % z_nat;
    assert y_nat == 2 * d_nat + (if sy[|sy|-1] == '0' then 0 else 1);
    IntStrInverse(r_nat);
    var t2 := Int2Str(r_nat);
    if sy[|sy|-1] == '0' {
      res := t2;
      assert Str2Int(res) == Exp_int(x_nat, y_nat) % z_nat;
    } else {
      var xt_nat := x_nat * Str2Int(t2);
      var r2_nat := xt_nat % z_nat;
      assert r2_nat == Exp_int(x_nat, 2 * d_nat + 1) % z_nat;
      IntStrInverse(r2_nat);
      res := Int2Str(r2_nat);
      assert Str2Int(res) == Exp_int(x_nat, y_nat) % z_nat;
    }
  }
  assert Str2Int(res) == Exp_int(x_nat, y_nat) % z_nat;
}
// </vc-code>

