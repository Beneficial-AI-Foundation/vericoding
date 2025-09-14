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

method Mul(s1: string, s2: string) returns (res: string)
  requires ValidBitString(s1) && ValidBitString(s2)
  ensures ValidBitString(res)
  ensures Str2Int(res) == Str2Int(s1) * Str2Int(s2)
{
  assume{:axiom} false;
}

// <vc-helpers>
function NatToStr(n: nat): string
{
  if n == 0 then "0"
  else if n == 1 then "1"
  else NatToStr(n / 2) + (if n % 2 == 1 then "1" else "0")
}

function Str2Int_prog(s: string): nat
  requires ValidBitString(s)
  decreases s
{
  if |s| == 0 then 0 else 2 * Str2Int_prog(s[0..|s|-1]) + (if s[|s|-1] == '1' then 1 else 0)
}

lemma Str2IntLem(s: string)
  requires ValidBitString(s)
  ensures Str2Int(s) == Str2Int_prog(s)
{
  if |s| == 0 {
  } else {
    Str2IntLem(s[0..|s|-1]);
    calc {
      Str2Int(s);
    == 2 * Str2Int(s[0..|s|-1]) + (if s[|s|-1] == '1' then 1 else 0);
    == 2 * Str2Int_prog(s[0..|s|-1]) + (if s[|s|-1] == '1' then 1 else 0);
    == Str2Int_prog(s);
    }
  }
}

lemma {:induction n} Str2IntNatToStrCorrect(n: nat)
  ensures ValidBitString(NatToStr(n))
  ensures Str2Int(NatToStr(n)) == n
{
  if n == 0 {
  } else if n == 1 {
  } else {
    Str2IntNatToStrCorrect(n / 2);
    var s1 := NatToStr(n / 2);
    var bit := if n % 2 == 1 then '1' else '0';
    var s := s1 + [bit];
    assert s == NatToStr(n);
    assert Str2Int(s) == 2 * Str2Int(s1) + (if bit == '1' then 1 else 0);
  }
}

ghost function Exp_mod(base: nat, exp: nat, m: nat): nat
  requires m > 0
  decreases exp
{
  if exp == 0 then 1
  else (base * Exp_mod(base, exp - 1, m)) % m
}

lemma Exp_mod_correct(base: nat, exp: nat, m: nat)
  requires m > 0
  ensures Exp_mod(base, exp, m) == Exp_int(base, exp) % m
{
  if exp == 0 {
  } else {
    Exp_mod_correct(base, exp - 1, m);
    calc {
      Exp_mod(base, exp, m);
    == (base * Exp_mod(base, exp - 1, m)) % m;
    == (base * (Exp_int(base, exp - 1) % m)) % m;
    == ((base % m) * (Exp_int(base, exp - 1) % m)) % m;
    == Exp_int(base, exp) % m;
    }
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
  var x: nat;
  x := Str2Int_prog(sx);
  var y: nat;
  y := Str2Int_prog(sy);
  var m: nat;
  m := Str2Int_prog(sz);
  Str2IntLem(sx);
  Str2IntLem(sy);
  Str2IntLem(sz);
  Exp_mod_correct(x, y, m);
  var result: nat;
  result := 1;
  var base: nat;
  base := x % m;
  var exp: nat;
  exp := y;
  while exp > 0
    invariant ValidBitString(NatToStr(result))
    invariant result >= 0 && result < m
    invariant base >= 0 && base < m
    invariant exp >= 0 && exp <= y
    invariant (result * Exp_mod(base, exp, m)) % m == Exp_mod(x, y, m) % m
    decreases exp
  {
    if exp % 2 == 1 {
      result := (result * base) % m;
    }
    base := (base * base) % m;
    exp := exp / 2;
  }
  Str2IntNatToStrCorrect(result);
  res := NatToStr(result);
  Str2IntLem(NatToStr(result));
}
// </vc-code>

