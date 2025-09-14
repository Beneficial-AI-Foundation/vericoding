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

method Add(s1: string, s2: string) returns (res: string)
  requires ValidBitString(s1) && ValidBitString(s2)
  ensures ValidBitString(res)
  ensures Str2Int(res) == Str2Int(s1) + Str2Int(s2)
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
lemma {:auto} Exp_succ(x: nat, y: nat)
  ensures Exp_int(x, y + 1) == x * Exp_int(x, y)
{
  assert y + 1 != 0;
  assert Exp_int(x, y + 1) == x * Exp_int(x, y);
}

lemma {:auto} Str2Int_One()
  ensures ValidBitString("1")
  ensures Str2Int("1") == 1
{
  assert ValidBitString("1");
  assert ValidBitString("");
  assert Str2Int("") == 0;
  assert Str2Int("1") == 1;
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
  call Str2Int_One();
  var acc: string := "1";
  var i: nat := 0;
  while i < Str2Int(sy)
    invariant ValidBitString(acc)
    invariant Str2Int(acc) == Exp_int(Str2Int(sx), i)
    invariant i <= Str2Int(sy)
    decreases Str2Int(sy) - i
  {
    var prod: string;
    call Mul(sx, acc) returns (prod);
    assert Str2Int(prod) == Str2Int(sx) * Str2Int(acc);
    assert Str2Int(prod) == Str2Int(sx) * Exp_int(Str2Int(sx), i);
    call Exp_succ(Str2Int(sx), i);
    assert Exp_int(Str2Int(sx), i + 1) == Str2Int(sx) * Exp_int(Str2Int(sx), i);
    acc := prod;
    i := i + 1;
  }
  var q: string;
  var r: string;
  call DivMod(acc, sz) returns (q, r);
  res := r;
}
// </vc-code>

