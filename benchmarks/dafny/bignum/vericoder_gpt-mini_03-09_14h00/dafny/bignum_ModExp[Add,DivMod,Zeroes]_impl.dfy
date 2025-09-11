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

method Zeros(n: nat) returns (s: string)
  ensures |s| == n
  ensures ValidBitString(s)
  ensures Str2Int(s) == 0
  ensures AllZero(s)
{
  assume{:axiom} false;
}

// <vc-helpers>
function Int2Str(n: nat): string
  ensures ValidBitString(Int2Str(n))
  ensures Str2Int(Int2Str(n)) == n
  decreases n
{
  if n == 0 then "" else Int2Str(n / 2) + (if n % 2 == 1 then "1" else "0")
}

lemma ValidBitString_prefix(s: string, m: int)
  requires ValidBitString(s)
  requires 0 <= m <= |s|
  ensures ValidBitString(s[0..m])
{
  assert forall k | 0 <= k < m :: s[k] == '0' || s[k] == '1';
}

lemma Str2Int_snoc(s: string)
  requires ValidBitString(s)
  requires |s| > 0
  ensures Str2Int(s) == 2 * Str2Int(s[0..|s|-1]) + (if s[|s|-1] == '1' then 1 else 0)
  decreases s
{
  assert Str2Int(s) == (if |s| == 0 then 0 else 2 * Str2Int(s[0..|s|-1]) + (if s[|s|-1] == '1' then 1 else 0));
}

lemma Str2Int_snoc_index(s: string, i: int)
  requires ValidBitString(s)
  requires 0 <= i < |s|
  ensures Str2Int(s[0..i+1]) == 2 * Str2Int(s[0..i]) + (if s[i] == '1' then 1 else 0)
{
  var s2 := s[0..i+1];
  assert |s2| == i+1;
  assert i+1 > 0;
  assert s2[|s2|-1] == s[i];
  assert s2[0..|s2|-1] == s[0..i];
  assert Str2Int(s2) == (if |s2| == 0 then 0 else 2 * Str2Int(s2[0..|s2|-1]) + (if s2[|s2|-1] == '1' then 1 else 0));
  assert Str2Int(s2) == 2 * Str2Int(s2[0..|s2|-1]) + (if s2[|s2|-1] == '1' then 1 else 0);
  assert Str2Int(s[0..i+1]) == 2 * Str2Int(s[0..i]) + (if s[i] == '1' then 1 else 0);
}

method Str2Int_nonghost(s: string) returns (n: nat)
  requires ValidBitString(s)
  ensures n == Str2Int(s)
  decreases s
{
  n := 0;
  var i := 0;
  while i < |s|
    invariant 0 <= i <= |s|
    invariant ValidBitString(s[0..i])
    invariant n == Str2Int(s[0..i])
    decreases |s| - i
  {
    var b := if s[i] == '1' then 1 else 0;
    Str2Int_snoc_index(s, i);
    n := n * 2 + b;
    i := i + 1;
  }
  // At this point i == |s|, so n == Str2Int(s[0..|s|]). Also s == s[0..|s|], hence n == Str2Int(s).
  assert s == s[0..|s|];
  assert n == Str2Int(s);
}

method ComputeExp(x: nat, y: nat) returns (r: nat)
  ensures r == Exp_int(x, y)
{
  r := 1;
  var i := 0;
  while i < y
    invariant 0 <= i <= y
    invariant r == Exp_int(x, i)
    decreases y - i
  {
    r := r * x;
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
  var xi := Str2Int_nonghost(sx);
  var yi := Str2Int_nonghost(sy);
  var zi := Str2Int_nonghost(sz);
  var pow := ComputeExp(xi, yi);
  var n := pow % zi;
  res := Int2Str(n);
}
// </vc-code>

