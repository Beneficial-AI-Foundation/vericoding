ghost function Exp_int(x: nat, y:nat): nat
{
  if y == 0 then 1 else x * Exp_int(x, y - 1)
}
predicate ValidBitString(s: string)
{
  // All characters must be '0' or '1'.
  forall i | 0 <= i < |s| :: s[i] == '0' || s[i] == '1'
}
ghost function Str2Int(s: string): nat
  requires ValidBitString(s)
  decreases s
{
  if |s| == 0 then  0  else  (2 * Str2Int(s[0..|s|-1]) + (if s[|s|-1] == '1' then 1 else 0))
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
lemma PrependBitLemma(b: nat, s: string)
  requires b == 0 || b == 1
  requires ValidBitString(s)
  ensures Str2Int((if b == 1 then "1" else "0") + s) == Exp_int(2, |s|) * b + Str2Int(s)
  decreases |s|
{
  if |s| == 0 {
  } else {
    var s1 := s[0..|s|-1];
    PrependBitLemma(b, s1);
  }
}

lemma Exp2_succ(n: nat)
  ensures Exp_int(2, n+1) == 2 * Exp_int(2, n)
  decreases n
{
  if n == 0 {
  } else {
    Exp2_succ(n-1);
  }
}

lemma Exp_square(x: nat, a: nat)
  ensures Exp_int(x, a) * Exp_int(x, a) == Exp_int(x, 2 * a)
  decreases a
{
  if a == 0 {
  } else {
    Exp_square(x, a-1);
  }
}

lemma AddMulMod(u: nat, k: nat, m: nat)
  requires m > 0
  ensures (u + m*k) % m == u % m
{
  var qu := u / m;
  var ru := u % m;
  assert u == qu*m + ru;
  assert (u + m*k) == (qu + k) * m + ru;
  assert (u + m*k) % m == ru;
  assert u % m == ru;
}

lemma ModProduct(u: nat, v: nat, m: nat)
  requires m > 0
  ensures (u % m * v % m) % m == (u*v) % m
{
  var qu := u / m;
  var ru := u % m;
  var qv := v / m;
  var rv := v % m;
  assert u == qu*m + ru;
  assert v == qv*m + rv;
  assert u*v == (qu*m + ru) * (qv*m + rv);
  assert u*v == ru*rv + m*(qu*qv*m + qu*rv + qv*ru);
  AddMulMod(ru*rv, qu*qv*m + qu*rv + qv*ru, m);
  assert (u*v) % m == (ru*rv) % m;
  assert (u % m * v % m) % m == (ru * rv) % m;
}

lemma AppendBitLemma(s: string, b: nat)
  requires b == 0 || b == 1
  requires ValidBitString(s)
  ensures ValidBitString(s + (if b == 1 then "1" else "0"))
  ensures Str2Int(s + (if b == 1 then "1" else "0")) == 2 * Str2Int(s) + b
  decreases |s|
{
  if |s| == 0 {
  } else {
  }
}

function Str2Int_impl(s: string): nat
  requires ValidBitString(s)
  decreases s
{
  if |s| == 0 then  0  else  (2 * Str2Int_impl(s[0..|s|-1]) + (if s[|s|-1] == '1' then 1 else 0))
}

lemma Str2Int_impl_eq(s: string)
  requires ValidBitString(s)
  ensures Str2Int_impl(s) == Str2Int(s)
  decreases s
{
  if |s| == 0 {
  } else {
    Str2Int_impl_eq(s[0..|s|-1]);
  }
}

function IntToBitString(u: nat): string
  decreases u
{
  if u == 0 then "" else
    if u % 2 == 0 then IntToBitString(u/2) + "0" else IntToBitString(u/2) + "1"
}

lemma IntToBitString_spec(u: nat)
  ensures ValidBitString(IntToBitString(u))
  ensures Str2Int(IntToBitString(u)) == u
  decreases u
{
  if u == 0 {
  } else {
    IntToBitString_spec(u/2);
    var s := IntToBitString(u/2);
    var b := u % 2;
    assert b == 0 || b == 1;
    // From recursive spec we have ValidBitString(s) and Str2Int(s) == u/2
    assert ValidBitString(s);
    assert Str2Int(s) == u/2;
    AppendBitLemma(s, b);
    // By definition of IntToBitString, IntToBitString(u) == s + (if b==1 then "1" else "0")
    assert IntToBitString(u) == s + (if b == 1 then "1" else "0");
    // Combine to get value equality
    assert Str2Int(IntToBitString(u)) == 2 * Str2Int(s) + b;
    var q := u/2;
    var r := u%2;
    assert u == q*2 + r;
    assert Str2Int(s) == q;
    assert Str2Int(IntToBitString(u)) == u;
  }
}
// </vc-helpers>

// <vc-spec>
method ModExpPow2(sx: string, sy: string, n: nat, sz: string) returns (res: string)
  requires ValidBitString(sx) && ValidBitString(sy) &&  ValidBitString(sz)
  // sy is power of 2 or zero
  requires Str2Int(sy) == Exp_int(2,n) || Str2Int(sy) == 0
  requires |sy| == n+1
  requires Str2Int(sz) > 1
  ensures ValidBitString(res)
  ensures Str2Int(res) == Exp_int(Str2Int(sx), Str2Int(sy)) % Str2Int(sz)
  decreases n
// </vc-spec>
// <vc-code>
{
  var m := Str2Int_impl(sz);
  var x := Str2Int_impl(sx);
  var e := Str2Int_impl(sy);
  Str2Int_impl_eq(sz);
  Str2Int_impl_eq(sx);
  Str2Int_impl_eq(sy);
  assert m == Str2Int(sz);
  assert x == Str2Int(sx);
  assert e == Str2Int(sy);
  assert m > 0;

  if e == 0 {
    var rr := 1 % m;
    res := IntToBitString(rr);
    return;
  }
  var curPow := x % m;
  var i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant curPow < m
    invariant curPow == Exp_int(x, Exp_int(2, i)) % m
    decreases n - i
  {
    var oldcur := curPow;
    curPow := (oldcur * oldcur) % m;

    assert oldcur == Exp_int(x, Exp_int(2, i)) % m;

    ModProduct(Exp_int(x, Exp_int(2, i)), Exp_int(x, Exp_int(2, i)), m);
    assert (oldcur * oldcur) % m == (Exp_int(x, Exp_int(2, i)) * Exp_int(x, Exp_int(2, i))) % m;

    Exp_square(x, Exp_int(2, i));
    assert Exp_int(x, Exp_int(2, i)) * Exp_int(x, Exp_int(2, i)) == Exp_int(x, 2 * Exp_int(2, i));

    Exp2_succ(i);
    assert Exp_int(2, i+1) == 2 * Exp_int(2, i);

    assert curPow == Exp_int(x, Exp_int(2, i+1)) % m;

    i := i + 1;
  }
  res := IntToBitString(curPow);
}
// </vc-code>

