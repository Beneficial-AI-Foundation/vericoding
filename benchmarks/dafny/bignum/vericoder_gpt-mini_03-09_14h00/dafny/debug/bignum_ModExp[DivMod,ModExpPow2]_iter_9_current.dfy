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
lemma AddMod(a: nat, b: nat, m: nat)
  requires m > 0
  ensures (a + b) % m == (a % m + b % m) % m
{
  var qa := a / m; var ra := a % m;
  var qb := b / m; var rb := b % m;
  assert a == m * qa + ra;
  assert b == m * qb + rb;
  assert a + b == m * (qa + qb) + (ra + rb);
  assert (a + b) % m == (ra + rb) % m;
  assert (a % m + b % m) % m == (ra + rb) % m;
}

lemma MulMod(x: nat, y: nat, m: nat)
  requires m > 0
  decreases y
  ensures (x * y) % m == ((x % m) * y) % m
{
  if y == 0 {
    assert (x * 0) % m == 0;
    assert ((x % m) * 0) % m == 0;
  } else {
    MulMod(x, y - 1, m);
    // x*y == x*(y-1) + x
    assert x * y == x * (y - 1) + x;
    AddMod(x * (y - 1), x, m);
    assert (x * y) % m == ((x * (y - 1)) % m + x % m) % m;
    // Replace (x*(y-1))%m using IH
    assert ((x * (y - 1)) % m) == (((x % m) * (y - 1)) % m);
    assert (x * y) % m == ((((x % m) * (y - 1)) % m) + x % m) % m;
    // Now ((x % m) * (y - 1) + x % m) == (x % m) * y
    assert ((x % m) * (y - 1) + x % m) == ((x % m) * y);
    // Apply AddMod to these two terms
    AddMod(((x % m) * (y - 1)), x % m, m);
    assert ((((x % m) * (y - 1)) % m + (x % m) % m) % m) == (((x % m) * y) % m);
    // x % m % m == x % m
    assert (x % m) % m == x % m;
    assert (x * y) % m == (((x % m) * y) % m);
  }
}

ghost function IntToBitString(v: nat) returns (result: string)
  ensures ValidBitString(result)
  ensures Str2Int(result) == v
  decreases v
{
  if v == 0 then result := "" else
    var q := v / 2;
    var r := v % 2;
    var prefix := IntToBitString(q);
    result := prefix + (if r == 1 then "1" else "0")
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
  var b := Str2Int(sx);
  var exp := Str2Int(sy);
  var m := Str2Int(sz);
  var e := exp;
  var acc := 1 % m;
  // Invariant: acc == Exp_int(b, exp - e) % m
  while e > 0
    invariant 0 <= e
    invariant acc == Exp_int(b, exp - e) % m
    decreases e
  {
    var oldE := e;
    var oldAcc := acc;
    acc := (acc * b) % m;
    // oldAcc == Exp_int(b, exp - oldE) % m by the invariant before the update
    assert oldAcc == Exp_int(b, exp - oldE) % m;
    // So acc == ((Exp_int(b, exp - oldE) % m) * b) % m
    assert acc == ((Exp_int(b, exp - oldE) % m) * b) % m;
    MulMod(Exp_int(b, exp - oldE), b, m);
    // MulMod gives equality with (Exp_int(...) * b) % m
    assert acc == (Exp_int(b, exp - oldE) * b) % m;
    assert Exp_int(b, exp - oldE + 1) == Exp_int(b, exp - oldE) * b;
    assert acc == Exp_int(b, exp - oldE + 1) % m;
    e := oldE - 1;
  }
  res := IntToBitString(acc);
}
// </vc-code>

