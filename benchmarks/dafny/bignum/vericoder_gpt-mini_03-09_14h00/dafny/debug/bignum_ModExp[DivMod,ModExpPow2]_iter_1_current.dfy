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
lemma MulMod(x: nat, y: nat, m: nat)
  requires m > 0
  ensures (x*y) % m == ((x % m) * y) % m
{
  var q := x / m;
  var r := x % m;
  assert x == m*q + r;
  assert x*y == m*(q*y) + r*y;
  assert (m*(q*y)) % m == 0;
  assert (x*y) % m == (r*y) % m;
  assert ((x % m) * y) % m == (r*y) % m;
}

lemma Exp_step(a: nat, i: nat)
  ensures Exp_int(a, i+1) == a * Exp_int(a, i)
{
  // By definition of Exp_int
  if i == 0 {
    assert Exp_int(a,1) == a * Exp_int(a,0);
  } else {
    assert Exp_int(a, i+1) == a * Exp_int(a, i);
  }
}

method Parse(s: string) returns (n: nat)
  requires ValidBitString(s)
  ensures n == Str2Int(s)
{
  n := 0;
  var i := 0;
  while i < |s|
    decreases |s| - i
    invariant 0 <= i <= |s|
    invariant n == Str2Int(s[..i])
  {
    n := 2 * n + (if s[i] == '1' then 1 else 0);
    i := i + 1;
  }
}

method ToBitString(x: nat) returns (s: string)
  ensures Str2Int(s) == x
  ensures ValidBitString(s)
{
  if x == 0 {
    s := "0";
    return;
  }
  ghost var orig := x;
  var cur := x;
  s := "";
  while cur > 0
    decreases cur
    invariant 0 <= cur <= orig
    invariant ValidBitString(s)
    invariant orig == cur * Exp_int(2, |s|) + Str2Int(s)
  {
    var b := cur % 2;
    if b == 1 {
      s := "1" + s;
    } else {
      s := "0" + s;
    }
    cur := cur / 2;
  }
  assert cur == 0;
  assert orig == Str2Int(s);
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
  var a := Parse(sx);
  var e := Parse(sy);
  var m := Parse(sz);

  var resNat := 1 % m;
  var i := 0;
  while i < e
    decreases e - i
    invariant 0 <= i <= e
    invariant resNat == Exp_int(a, i) % m
  {
    // Prepare proofs to justify the update of resNat
    assert resNat == Exp_int(a, i) % m;
    MulMod(Exp_int(a, i), a, m);
    Exp_step(a, i);
    // Now update numerically
    resNat := (resNat * a) % m;
    i := i + 1;
  }

  res := ToBitString(resNat);
}
// </vc-code>

