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

// <vc-helpers>
method BitStringToNat(s: string) returns (n: nat)
  requires ValidBitString(s)
  ensures n == Str2Int(s)
{
  var i := 0;
  n := 0;
  while i < |s|
    decreases |s| - i
    invariant 0 <= i <= |s|
    invariant ValidBitString(s)
    invariant n == Str2Int(s[0..i])
  {
    var bit := if s[i] == '1' then 1 else 0;
    n := 2 * n + bit;
    i := i + 1;
  }
  assert n == Str2Int(s);
}

method NatToBitString(n: nat) returns (s: string)
  ensures ValidBitString(s)
  ensures Str2Int(s) == n
  decreases n
{
  if n == 0 {
    s := "0";
    return;
  }
  if n == 1 {
    s := "1";
    return;
  }
  var prefix := NatToBitString(n / 2);
  var d := n % 2;
  s := prefix + (if d == 1 then "1" else "0");
  assert Str2Int(prefix) == n / 2;
  assert Str2Int(s) == 2 * Str2Int(prefix) + (if d == 1 then 1 else 0);
  assert Str2Int(s) == 2 * (n / 2) + (n % 2);
  assert Str2Int(s) == n;
  assert ValidBitString(s);
}

method Add_impl(s1: string, s2: string) returns (res: string)
  requires ValidBitString(s1) && ValidBitString(s2)
  ensures ValidBitString(res)
  ensures Str2Int(res) == Str2Int(s1) + Str2Int(s2)
{
  var n1 := BitStringToNat(s1);
  var n2 := BitStringToNat(s2);
  var sum := n1 + n2;
  res := NatToBitString(sum);
  assert Str2Int(res) == sum;
  assert ValidBitString(res);
}

method DivMod_impl(dividend: string, divisor: string) returns (quotient: string, remainder: string)
  requires ValidBitString(dividend) && ValidBitString(divisor)
  requires Str2Int(divisor) > 0
  ensures ValidBitString(quotient) && ValidBitString(remainder)
  ensures Str2Int(quotient) == Str2Int(dividend) / Str2Int(divisor)
  ensures Str2Int(remainder) == Str2Int(dividend) % Str2Int(divisor)
{
  var dv := BitStringToNat(dividend);
  var ds := BitStringToNat(divisor);
  var q := dv / ds;
  var r := dv % ds;
  quotient := NatToBitString(q);
  remainder := NatToBitString(r);
  assert Str2Int(quotient) == q;
  assert Str2Int(remainder) == r;
  assert ValidBitString(quotient) && ValidBitString(remainder);
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
      var _, r := DivMod_impl("1", sz);
      res := r;
    } else {
      var _, r := DivMod_impl(sx, sz);
      res := r;
    }
    return;
  }

  var syPrefix := sy[0..|sy|-1];
  var last := sy[|sy|-1];

  var t := ModExp(sx, syPrefix, sz);
  var t2 := Mul(t, t);
  var _, r := DivMod_impl(t2, sz);

  ghost var x := Str2Int(sx);
  ghost var m := Str2Int(sz);
  ghost var yp := Str2Int(syPrefix);
  ghost var b := if last == '1' then 1 else 0;
  ghost var A := Exp_int(x, yp);

  assert Str2Int(t) == A % m;
  assert Str2Int(t2) == Str2Int(t) * Str2Int(t);
  assert Str2Int(r) == Str2Int(t2) % m;

  MulModIdentity(A, A, m);
  assert Str2Int(r) == (A * A) % m;

  Exp_bin_pow(x, yp, b);
  if last == '1' {
    var t3 := Mul(r, sx);
    var _, r2 := DivMod_impl(t3, sz);
    assert Str2Int(t3) == Str2Int(r) * Str2Int(sx);
    assert Str2Int(r2) == Str2Int(t3) % m;

    MulModIdentity(A * A, x, m);
    MulModIdentity(Str2Int(r), Str2Int(sx), m);
    assert Str2Int(r2) == Exp_int(x, 2 * yp + 1) % m;
    res := r2;
  } else {
    assert Str2Int(r) == Exp_int(x, 2 * yp) % m;
    res := r;
  }
}
// </vc-code>

