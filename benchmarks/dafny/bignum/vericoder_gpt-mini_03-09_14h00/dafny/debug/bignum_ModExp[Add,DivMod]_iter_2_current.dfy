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
method Mul(a: string, b: string) returns (prod: string)
  requires ValidBitString(a) && ValidBitString(b)
  ensures ValidBitString(prod)
  ensures Str2Int(prod) == Str2Int(a) * Str2Int(b)
{
  var aa := a;
  var bb := b;
  prod := "0";
  assert ValidBitString(prod);
  // Invariant: prod + aa * bb == a * b
  while |bb| > 0
    decreases |bb|
    invariant ValidBitString(aa) && ValidBitString(bb) && ValidBitString(prod)
    invariant Str2Int(prod) + Str2Int(aa) * Str2Int(bb) == Str2Int(a) * Str2Int(b)
  {
    if bb[|bb|-1] == '1' {
      var newProd: string;
      call Add(prod, aa) returns (newProd);
      prod := newProd;
    }
    var newAa: string;
    call Add(aa, aa) returns (newAa);
    aa := newAa;
    bb := bb[0..|bb|-1];
  }
  // When bb is empty, Str2Int(prod) == Str2Int(a)*Str2Int(b) holds by invariant.
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
      var r: string;
      call DivMod("1", sz) returns (_, r);
      res := r;
    } else {
      var r: string;
      call DivMod(sx, sz) returns (_, r);
      res := r;
    }
    return;
  }

  var syPrefix := sy[0..|sy|-1];
  var last := sy[|sy|-1];

  var t: string;
  call ModExp(sx, syPrefix, sz) returns (t);
  var t2: string;
  call Mul(t, t) returns (t2);
  var r: string;
  call DivMod(t2, sz) returns (_, r);
  if last == '1' {
    var t3: string;
    call Mul(r, sx) returns (t3);
    var rfinal: string;
    call DivMod(t3, sz) returns (_, rfinal);
    res := rfinal;
  } else {
    res := r;
  }
}
// </vc-code>

