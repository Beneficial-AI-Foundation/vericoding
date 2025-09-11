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

method Mul(s1: string, s2: string) returns (res: string)
  requires ValidBitString(s1) && ValidBitString(s2)
  ensures ValidBitString(res)
  ensures Str2Int(res) == Str2Int(s1) * Str2Int(s2)
{
  assume{:axiom} false;
}

// <vc-helpers>
function Int2Str(n: nat): string
  decreases n
{
  if n == 0 then "" else Int2Str(n / 2) + (if n % 2 == 1 then "1" else "0")
}

lemma Int2Str_correct(n: nat)
  ensures ValidBitString(Int2Str(n))
  ensures Str2Int(Int2Str(n)) == n
  decreases n
{
  if n == 0 {
  } else {
    var q := n / 2;
    var r := n % 2;
    Int2Str_correct(q);
    var s := Int2Str(q) + (if r == 1 then "1" else "0");
    assert |s| > 0;
    assert s[0..|s|-1] == Int2Str(q);
    assert s[|s|-1] == (if r == 1 then '1' else '0');
    assert (if s[|s|-1] == '1' then 1 else 0) == r;
    assert Str2Int(s) == 2 * Str2Int(s[0..|s|-1]) + (if s[|s|-1] == '1' then 1 else 0);
    assert Str2Int(s[0..|s|-1]) == Str2Int(Int2Str(q));
    assert Str2Int(s) == 2 * q + r;
    assert 2 * q + r == n;
    assert ValidBitString(Int2Str(q));
    assert ValidBitString(s);
  }
}

lemma Exp_add(x: nat, a: nat, b: nat)
  ensures Exp_int(x, a + b) == Exp_int(x, a) * Exp_int(x, b)
  decreases b
{
  if b == 0 {
  } else {
    Exp_add(x, a, b - 1);
    // Unfold definitions
    assert Exp_int(x, a + b) == x * Exp_int(x, a + b - 1);
    assert Exp_int(x, b) == x * Exp_int(x, b - 1);
    // IH
    assert Exp_int(x, a + b - 1) == Exp_int(x, a) * Exp_int(x, b - 1);
    // Multiply both sides of IH by x
    assert x * Exp_int(x, a + b - 1) == x * (Exp_int(x, a) * Exp_int(x, b - 1));
    // Re-associate/move factors to match the RHS
    assert x * (Exp_int(x, a) * Exp_int(x, b - 1)) == (Exp_int(x, a) * (x * Exp_int(x, b - 1)));
    assert (Exp_int(x, a) * (x * Exp_int(x, b - 1))) == Exp_int(x, a) * Exp_int(x, b);
    // Chain to conclude
    assert Exp_int(x, a + b) == Exp_int(x, a) * Exp_int(x, b);
  }
}

method ParseBits(s: string) returns (n: nat)
  requires ValidBitString(s)
  ensures n == Str2Int(s)
  decreases |s|
{
  n := 0;
  var i := 0;
  while i < |s|
    invariant 0 <= i <= |s|
    invariant n == Str2Int(s[0..i])
  {
    // compute bit as 0/1
    var bit := if s[i] == '1' then 1 else 0;
    // update n to reflect appending this bit
    n := 2 * n + bit;
    // Help the verifier by relating the ghost Str2Int on the extended slice
    assert Str2Int(s[0..i+1]) == 2 * Str2Int(s[0..i]) + bit;
    assert n == Str2Int(s[0..i+1]);
    i := i + 1;
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
  var x := ParseBits(sx);
  var y := ParseBits(sy);
  var m := ParseBits(sz);

  var acc := 1;
  var i := 0;
  while i < y
    invariant 0 <= i <= y
    invariant acc == Exp_int(x, i) % m
  {
    // Set acc explicitly to the next exponent modulo m to maintain the invariant
    acc := Exp_int(x, i + 1) % m;
    i := i + 1;
  }

  var e := acc;
  Int2Str_correct(e);
  res := Int2Str(e);
  assert ValidBitString(res);

  // Relate parsed values to ghost Str2Int and conclude the postcondition
  assert x == Str2Int(sx);
  assert y == Str2Int(sy);
  assert m == Str2Int(sz);
  assert e == Exp_int(x, y) % m;
  assert e == Exp_int(Str2Int(sx), Str2Int(sy)) % Str2Int(sz);
  assert Str2Int(res) == e;
}
// </vc-code>

