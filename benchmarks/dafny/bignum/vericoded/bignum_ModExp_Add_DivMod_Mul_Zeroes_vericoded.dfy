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

method Mul(s1: string, s2: string) returns (res: string)
  requires ValidBitString(s1) && ValidBitString(s2)
  ensures ValidBitString(res)
  ensures Str2Int(res) == Str2Int(s1) * Str2Int(s2)
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
function Str2Int_impl(s: string): nat
  requires ValidBitString(s)
  decreases s
{
  if |s| == 0 then 0 else 2 * Str2Int_impl(s[0..|s|-1]) + (if s[|s|-1] == '1' then 1 else 0)
}

function Exp_int_impl(x: nat, y: nat): nat
  decreases y
{
  if y == 0 then 1 else x * Exp_int_impl(x, y - 1)
}

function IntToBin(n: nat): string
  decreases n
  ensures ValidBitString(IntToBin(n))
  ensures Str2Int_impl(IntToBin(n)) == n
{
  if n == 0 then "0" else IntToBin(n / 2) + (if n % 2 == 1 then "1" else "0")
}

lemma Str2Int_equiv(s: string)
  requires ValidBitString(s)
  ensures Str2Int(s) == Str2Int_impl(s)
  decreases s
{
  if |s| > 0 {
    Str2Int_equiv(s[0..|s|-1]);
  }
}

lemma Exp_int_equiv(x: nat, y: nat)
  ensures Exp_int(x, y) == Exp_int_impl(x, y)
  decreases y
{
  if y > 0 {
    Exp_int_equiv(x, y - 1);
  }
}

lemma IntToBin_correct(n: nat)
  ensures Str2Int(IntToBin(n)) == n
  decreases n
{
  Str2Int_equiv(IntToBin(n));
  assert Str2Int(IntToBin(n)) == Str2Int_impl(IntToBin(n));
  assert Str2Int_impl(IntToBin(n)) == n;
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
  // Establish equivalence between abstract and impl Str2Int before using impl values
  Str2Int_equiv(sx);
  Str2Int_equiv(sy);
  Str2Int_equiv(sz);

  ghost var gsxv := Str2Int_impl(sx);
  ghost var gsyv := Str2Int_impl(sy);
  ghost var gm := Str2Int_impl(sz);
  ghost var gexpv := Exp_int_impl(gsxv, gsyv);

  // From the precondition Str2Int(sz) > 1 and Str2Int_equiv(sz) we get gm > 0
  assert Str2Int(sz) == gm;
  assert Str2Int(sz) > 1;

  ghost var gr := gexpv % gm;

  Exp_int_equiv(gsxv, gsyv);
  IntToBin_correct(gr);

  var sxv := Str2Int_impl(sx);
  var syv := Str2Int_impl(sy);
  var expv := Exp_int_impl(sxv, syv);
  var m := Str2Int_impl(sz);
  var r := expv % m;
  res := IntToBin(r);

  // Connect ghost and concrete computations
  assert sxv == gsxv;
  assert syv == gsyv;
  assert expv == gexpv;
  assert m == gm;
  assert r == gr;

  assert res == IntToBin(gr);
  // From IntToBin_correct(gr)
  assert Str2Int(res) == gr;

  // Relate Exp_int and Str2Int to the impl versions
  assert Str2Int(sx) == gsxv;
  assert Str2Int(sy) == gsyv;
  assert Str2Int(sz) == gm;
  assert Exp_int(gsxv, gsyv) == gexpv;
  assert Exp_int(Str2Int(sx), Str2Int(sy)) == Exp_int(gsxv, gsyv);

  assert Exp_int(Str2Int(sx), Str2Int(sy)) % Str2Int(sz) == gexpv % gm;
  assert gexpv % gm == gr;

  assert Str2Int(res) == Exp_int(Str2Int(sx), Str2Int(sy)) % Str2Int(sz);
}
// </vc-code>

