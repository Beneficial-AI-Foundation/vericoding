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
function Bin2Nat(s: string): nat
  decreases s
{
  if |s| == 0 then 0 else 2 * Bin2Nat(s[0..|s|-1]) + (if s[|s|-1] == '1' then 1 else 0)
}

lemma Bin2Nat_eq_Str2Int(s: string)
  requires ValidBitString(s)
  ensures Bin2Nat(s) == Str2Int(s)
  decreases s
{
  if |s| == 0 {
  } else {
    Bin2Nat_eq_Str2Int(s[0..|s|-1]);
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
  var z := Bin2Nat(sz);
  // relate Bin2Nat and Str2Int for later proofs
  assert Bin2Nat(sz) == Str2Int(sz);
  if Bin2Nat(sy) == 0 {
    res := Nat2Str(1 % z);
    return;
  }
  // initial value
  var v := Bin2Nat(sx) % z;
  assert Bin2Nat(sx) == Str2Int(sx);
  assert v == Str2Int(sx) % z;
  var i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant v < z
    invariant v == Exp_int(Str2Int(sx), Exp_int(2, i)) % z
  {
    var oldv := v;
    ghost var big := Exp_int(2, i);
    // use lemmas about exponentiation and modular multiplication
    MulMod(Exp_int(Str2Int(sx), big), Exp_int(Str2Int(sx), big), z);
    Exp_add(Str2Int(sx), big, big);
    Exp2_double(i);
    v := (oldv * oldv) % z;
    assert v == (Exp_int(Str2Int(sx), big) * Exp_int(Str2Int(sx), big)) % z;
    assert (Exp_int(Str2Int(sx), big) * Exp_int(Str2Int(sx), big)) % z == Exp_int(Str2Int(sx), big + big) % z;
    assert big + big == Exp_int(2, i+1);
    assert v == Exp_int(Str2Int(sx), Exp_int(2, i+1)) % z;
    i := i + 1;
  }
  res := Nat2Str(v);
}
// </vc-code>

