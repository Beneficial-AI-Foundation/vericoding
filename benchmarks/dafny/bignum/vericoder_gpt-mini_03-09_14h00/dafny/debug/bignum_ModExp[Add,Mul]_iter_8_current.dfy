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
    // Prepare facts about the next character and concatenation
    SubstringValid(s, 0, i);
    SubstringValid(s, i, i + 1);
    StrConcatLemma(s[0..i], s[i..i+1]);
    SingleCharStrVal(s, i);
    // Update numeric value by appending the next bit
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

lemma StrConcatLemma(a: string, b: string)
  requires ValidBitString(a) && ValidBitString(b)
  ensures Str2Int(a + b) == Str2Int(a) * Exp_int(2, |b|) + Str2Int(b)
  decreases |b|
{
  if |b| == 0 {
    // trivial: a + "" = a, Exp_int(2,0)=1, Str2Int("")=0
  } else {
    var bprefix := b[0..|b|-1];
    var last := b[|b|-1..|b|];
    SubstringValid(b, 0, |b|-1);
    SubstringValid(b, |b|-1, |b|);
    // Inductive hypothesis for shorter bprefix
    StrConcatLemma(a, bprefix);
    // By definition of Str2Int on a non-empty string u = (a + bprefix) + last:
    // Str2Int(u) = 2 * Str2Int(u[0..|u|-1]) + Str2Int(last)
    assert Str2Int((a + bprefix) + last) == 2 * Str2Int(a + bprefix) + Str2Int(last);
    // For b = bprefix + last:
    assert Str2Int(b) == 2 * Str2Int(bprefix) + Str2Int(last);
    // Use induction to expand Str2Int(a + bprefix)
    assert Str2Int(a + bprefix) == Str2Int(a) * Exp_int(2, |b|-1) + Str2Int(bprefix);
    // Relate powers of two
    if |b| >= 1 {
      Exp2_mult(|b| - 1);
    }
    // Combine arithmetic equalities to reach the desired form
    assert 2 * Str2Int(a + bprefix) + Str2Int(last) ==
           2 * (Str2Int(a) * Exp_int(2, |b|-1) + Str2Int(bprefix)) + Str2Int(last);
    assert 2 * (Str2Int(a) * Exp_int(2, |b|-1)) == Str2Int(a) * Exp_int(2, |b|);
    assert 2 * Str2Int(bprefix) + Str2Int(last) == Str2Int(b);
    assert 2 * (Str2Int(a) * Exp_int(2, |b|-1) + Str2Int(bprefix)) + Str2Int(last) ==
           Str2Int(a) * Exp_int(2, |b|) + Str2Int(b);
    // Hence Str2Int(a + b) == Str2Int(a) * Exp_int(2, |b|) + Str2Int(b)
  }
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
    // Use exponent addition and modular multiplication facts to update the invariant
    assert resInt == Exp_int(x, prefixVal) % m;
    ExpAdd(x, prefixVal, prefixVal);
    MulMod(Exp_int(x, prefixVal), Exp_int(x, prefixVal), m);
    // From MulMod we have (Exp*Exp) % m == ((Exp % m) * (Exp % m)) % m
    assert tmp == ((Exp_int(x, prefixVal) % m) * (Exp_int(x, prefixVal) % m)) % m;
    assert tmp == (Exp_int(x, prefixVal) * Exp_int(x, prefixVal)) % m;
    assert tmp == Exp_int(x, prefixVal + prefixVal) % m;
    resInt := tmp;
    if sy[i] == '1' {
      // Multiply by x modulo m and maintain the invariant
      var before := resInt;
      var newtmp := (before * x) % m;
      // relate (before * x) % m with (Exp_int(...)*x) % m
      LeftMulMod(before, x, m);
      // before == Exp_int(x, prefixVal+prefixVal) % m
      assert before == Exp_int(x, prefixVal + prefixVal) % m;
      // combine to get newtmp == (Exp_int(...) * x) % m
      assert newtmp == ((Exp_int(x, prefixVal + prefixVal) % m) * (x % m)) % m;
      MulMod(Exp_int(x, prefixVal + prefixVal), x, m);
      assert newtmp == (Exp_int(x, prefixVal + prefixVal) * x) % m;
      ExpAdd(x, prefixVal + prefixVal, 1);
      assert newtmp == Exp_int(x, prefixVal + prefixVal + 1) % m;
      resInt := newtmp;
    }
    SubstringValid(sy, i, i + 1);
    StrConcatLemma(sy[0..i], sy[i..i+1]);
    SingleCharStrVal(sy, i);
    i := i + 1;
    SubstringValid(sy, 0, i);
  }
  res := Nat2Str(resInt);
  Nat2Str_correct(resInt);
}
// </vc-code>

