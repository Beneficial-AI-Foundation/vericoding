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

method Mul(s1: string, s2: string) returns (res: string)
  requires ValidBitString(s1) && ValidBitString(s2)
  ensures ValidBitString(res)
  ensures Str2Int(res) == Str2Int(s1) * Str2Int(s2)
{
  assume{:axiom} false;
}

// <vc-helpers>
function Str2Int_nonghost(s: string): nat
  decreases |s|
{
  if |s| == 0 then 0 else 2 * Str2Int_nonghost(s[0..|s|-1]) + (if s[|s|-1] == '1' then 1 else 0)
}

function Exp_int_nonghost(x: nat, y: nat): nat
  decreases y
{
  if y == 0 then 1 else x * Exp_int_nonghost(x, y - 1)
}

function Int2Str(n: nat): string
  decreases n
{
  if n == 0 then "" else Int2Str(n / 2) + (if n % 2 == 1 then "1" else "0")
}

lemma Str2Int_nonghost_eq(s: string)
  requires ValidBitString(s)
  ensures Str2Int_nonghost(s) == Str2Int(s)
  decreases |s|
{
  if |s| == 0 {
    assert Str2Int_nonghost(s) == 0;
    assert Str2Int(s) == 0;
  } else {
    Str2Int_nonghost_eq(s[0..|s|-1]);
    assert Str2Int_nonghost(s) ==
           2 * Str2Int_nonghost(s[0..|s|-1]) + (if s[|s|-1] == '1' then 1 else 0);
    assert Str2Int(s) ==
           2 * Str2Int(s[0..|s|-1]) + (if s[|s|-1] == '1' then 1 else 0);
    assert Str2Int_nonghost(s[0..|s|-1]) == Str2Int(s[0..|s|-1]);
    assert Str2Int_nonghost(s) == Str2Int(s);
  }
}

lemma Exp_int_nonghost_eq(x: nat, y: nat)
  ensures Exp_int_nonghost(x, y) == Exp_int(x, y)
  decreases y
{
  if y == 0 {
    assert Exp_int_nonghost(x, 0) == 1;
    assert Exp_int(x, 0) == 1;
  } else {
    Exp_int_nonghost_eq(x, y - 1);
    assert Exp_int_nonghost(x, y) == x * Exp_int_nonghost(x, y - 1);
    assert Exp_int(x, y) == x * Exp_int(x, y - 1);
    assert Exp_int_nonghost(x, y) == Exp_int(x, y);
  }
}

lemma Str2Int_append_bit(s: string, bit: string)
  requires ValidBitString(s)
  requires |bit| == 1
  requires bit[0] == '0' || bit[0] == '1'
  ensures Str2Int(s + bit) == 2 * Str2Int(s) + (if bit[0] == '1' then 1 else 0)
{
  assert |s + bit| == |s| + 1;
  assert (s + bit)[0..|s + bit| - 1] == s;
  assert (s + bit)[|s + bit| - 1] == bit[0];
  assert Str2Int(s + bit) ==
         2 * Str2Int((s + bit)[0..|s + bit| - 1]) + (if (s + bit)[|s + bit| - 1] == '1' then 1 else 0);
  assert Str2Int((s + bit)[0..|s + bit| - 1]) == Str2Int(s);
  assert (if (s + bit)[|s + bit| - 1] == '1' then 1 else 0) == (if bit[0] == '1' then 1 else 0);
  assert Str2Int(s + bit) == 2 * Str2Int(s) + (if bit[0] == '1' then 1 else 0);
}

lemma Int2Str_correct(n: nat)
  ensures ValidBitString(Int2Str(n))
  ensures Str2Int(Int2Str(n)) == n
  decreases n
{
  if n == 0 {
    assert Int2Str(0) == "";
    assert ValidBitString("");
    assert Str2Int("") == 0;
  } else {
    var q := n / 2;
    var r := n % 2;
    Int2Str_correct(q);
    assert ValidBitString(Int2Str(q));
    var bit := if r == 1 then "1" else "0";
    assert |bit| == 1;
    assert bit[0] == '0' || bit[0] == '1';
    Str2Int_append_bit(Int2Str(q), bit);
    assert Str2Int(Int2Str(q) + bit) == 2 * Str2Int(Int2Str(q)) + (if bit[0] == '1' then 1 else 0);
    assert Str2Int(Int2Str(q)) == q;
    assert 2 * q + r == n;
    assert Str2Int(Int2Str(q) + bit) == n;
    assert ValidBitString(Int2Str(q) + bit);
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
  // First relate string-to-int non-ghost functions to ghost ones so we can use their equalities.
  Str2Int_nonghost_eq(sx);
  Str2Int_nonghost_eq(sy);
  Str2Int_nonghost_eq(sz);

  // From the spec we know Str2Int(sz) > 1, so after the equality we know the non-ghost value is > 1,
  // which prevents division-by-zero in the subsequent modulo.
  assert Str2Int_nonghost(sz) == Str2Int(sz);
  assert Str2Int(sz) > 1;
  assert Str2Int_nonghost(sz) > 1;

  // Relate exponent functions
  assert Str2Int_nonghost(sx) == Str2Int(sx);
  assert Str2Int_nonghost(sy) == Str2Int(sy);
  Exp_int_nonghost_eq(Str2Int(sx), Str2Int(sy));
  // Now we can connect the non-ghost exponent to the ghost exponent.
  assert Exp_int_nonghost(Str2Int_nonghost(sx), Str2Int_nonghost(sy)) == Exp_int(Str2Int(sx), Str2Int(sy));

  // Safe to compute modulo since Str2Int_nonghost(sz) > 0
  var n := Exp_int_nonghost(Str2Int_nonghost(sx), Str2Int_nonghost(sy)) % Str2Int_nonghost(sz);
  res := Int2Str(n);
  Int2Str_correct(n);

  // Conclude the postcondition using the established equalities.
  assert Str2Int(res) == n;
  assert Str2Int(res) == Exp_int(Str2Int(sx), Str2Int(sy)) % Str2Int(sz);
}
// </vc-code>

