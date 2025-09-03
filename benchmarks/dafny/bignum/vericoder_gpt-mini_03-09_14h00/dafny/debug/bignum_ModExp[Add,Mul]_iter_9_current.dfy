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

method Mul(s1: string, s2: string) returns (res: string)
  requires ValidBitString(s1) && ValidBitString(s2)
  ensures ValidBitString(res)
  ensures Str2Int(res) == Str2Int(s1) * Str2Int(s2)
{
  assume{:axiom} false;
}

// <vc-helpers>
function Nat2Str(n: nat): string
  decreases n
{
  if n == 0 then "" else Nat2Str(n / 2) + (if n % 2 == 1 then "1" else "0")
}

lemma SubstringValid(s: string, i: int, j: int)
  requires ValidBitString(s)
  requires 0 <= i <= j <= |s|
  ensures ValidBitString(s[i..j])
{
  // Follows from the definition of ValidBitString (forall over indices).
}

method ToNat(s: string) returns (n: nat)
  requires ValidBitString(s)
  ensures n == Str2Int(s)
  decreases |s|
{
  n := 0;
  var i := 0;
  SubstringValid(s, 0, 0);
  while i < |s|
    invariant 0 <= i <= |s|
    invariant n == Str2Int(s[0..i])
    invariant ValidBitString(s[0..i])
    decreases |s| - i
  {
    SubstringValid(s, 0, i);
    SubstringValid(s, i, i + 1);
    SingleCharStrVal(s, i);
    // By definition of Str2Int on non-empty string u = s[0..i+1],
    // Str2Int(u) == 2 * Str2Int(u[0..|u|-1]) + Str2Int(u[|u|-1..|u|])
    assert Str2Int(s[0..i+1]) == 2 * Str2Int(s[0..i]) + Str2Int(s[i..i+1]);
    n := n * 2 + (if s[i] == '1' then 1 else 0);
    i := i + 1;
    SubstringValid(s, 0, i);
  }
}

lemma ExpAdd(x: nat, a: nat, b: nat)
  ensures Exp_int(x, a + b) == Exp_int(x, a) * Exp_int(x, b)
  decreases b
{
  if b == 0 {
  } else {
    ExpAdd(x, a, b - 1);
  }
}

lemma Exp2_mult(n: nat)
  ensures Exp_int(2, n + 1) == 2 * Exp_int(2, n)
{
  ExpAdd(2, n, 1);
}

lemma SingleCharStrVal(s: string, i: int)
  requires ValidBitString(s)
  requires 0 <= i < |s|
  ensures Str2Int(s[i..i+1]) == (if s[i] == '1' then 1 else 0)
{
  // Since s[i..i+1] has length 1, Str2Int of that substring equals the bit value.
}

lemma Nat2Str_correct(n: nat)
  ensures ValidBitString(Nat2Str(n)) && Str2Int(Nat2Str(n)) == n
  decreases n
{
  if n == 0 {
  } else {
    var q := n / 2;
    var r := n % 2;
    Nat2Str_correct(q);
  }
}

lemma MulMod(A: nat, B: nat, m: nat)
  requires m > 0
  ensures (A * B) % m == ((A % m) * (B % m)) % m
{
  var qA := A / m;
  var rA := A % m;
  var qB := B / m;
  var rB := B % m;
  assert A == m * qA + rA;
  assert B == m * qB + rB;
  assert A * B == (m * qA + rA) * (m * qB + rB);
  assert A * B == m * (qA * (m * qB + rB) + rA * qB) + rA * rB;
  assert (A * B) % m == (rA * rB) % m;
  assert (rA * rB) % m == ((A % m) * (B % m)) % m;
}

lemma LeftMulMod(a: nat, x: nat, m: nat)
  requires m > 0
  requires 0 <= a < m
  ensures (a * x) % m == (a * (x % m)) % m
{
  var q := x / m;
  var r := x % m;
  assert x == m * q + r;
  assert a * x == a * (m * q + r);
  assert a * x == m * (a * q) + a * r;
  assert (a * x) % m == (a * r) % m;
  assert (a * r) % m == (a * (x % m)) % m;
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
  var x := ToNat(sx);
  var m := ToNat(sz);
  var resInt := 1 % m;
  var i := 0;
  SubstringValid(sy, 0, 0);
  while i < |sy|
    invariant 0 <= i <= |sy|
    invariant 0 <= resInt < m
    invariant resInt == Exp_int(x, Str2Int(sy[0..i])) % m
    invariant ValidBitString(sy[0..i])
    decreases |sy| - i
  {
    var prefixVal := Str2Int(sy[0..i]);
    var tmp := (resInt * resInt) % m;
    assert resInt == Exp_int(x, prefixVal) % m;
    ExpAdd(x, prefixVal, prefixVal);
    MulMod(Exp_int(x, prefixVal), Exp_int(x, prefixVal), m);
    assert tmp == Exp_int(x, prefixVal + prefixVal) % m;
    resInt := tmp;
    if sy[i] == '1' {
      var before := resInt;
      var newtmp := (before * x) % m;
      LeftMulMod(before, x, m);
      assert before == Exp_int(x, prefixVal + prefixVal) % m;
      assert newtmp == (Exp_int(x, prefixVal + prefixVal) * x) % m;
      MulMod(Exp_int(x, prefixVal + prefixVal), x, m);
      ExpAdd(x, prefixVal + prefixVal, 1);
      assert newtmp == Exp_int(x, prefixVal + prefixVal + 1) % m;
      resInt := newtmp;
    }
    SubstringValid(sy, i, i + 1);
    SingleCharStrVal(sy, i);
    assert Str2Int(sy[0..i+1]) == 2 * prefixVal + Str2Int(sy[i..i+1]);
    i := i + 1;
    SubstringValid(sy, 0, i);
  }
  res := Nat2Str(resInt);
  Nat2Str_correct(resInt);
}
// </vc-code>

