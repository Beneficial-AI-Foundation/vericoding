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
function ModExp_int(x: nat, y: nat, z: nat): nat
  decreases y
  requires z > 1
  ensures ModExp_int(x, y, z) == Exp_int(x, y) % z
{
  if y == 0 then 1 % z
  else
    var half := ModExp_int(x, y / 2, z);
    var square := (half * half) % z;
    if y % 2 == 1 then (square * (x % z)) % z
    else square
}

function Int2Str(n: nat): string
  decreases n
  ensures ValidBitString(Int2Str(n))
  ensures Str2Int(Int2Str(n)) == n
{
  if n == 0 then "0" else Int2Str_aux(n)
}

function Int2Str_aux(n: nat): string
  decreases n
  ensures ValidBitString(Int2Str_aux(n))
  ensures Str2Int(Int2Str_aux(n)) == n
{
  if n == 0 then ""
  else 
    Int2Str_aux(n / 2) + (if n % 2 == 1 then "1" else "0")
}

lemma Int2StrStr2Int_ID(n: nat)
  ensures Str2Int(Int2Str(n)) == n
{
  if n == 0 {
    assert Int2Str(0) == "0";
    assert Str2Int("0") == 0;
  } else {
    Int2StrStr2Int_ID(n / 2);
    var s := Int2Str_aux(n);
    var half := n / 2;
    var half_s := Int2Str_aux(half);
    assert s == half_s + (if n % 2 == 1 then "1" else "0");
    assert Str2Int(s) == Str2Int(half_s) * 2 + (if n % 2 == 1 then 1 else 0);
    assert Str2Int(half_s) == half;
    assert half * 2 + (n % 2) == n;
  }
}

method Str2Int_method(s: string) returns (n: nat)
  requires ValidBitString(s)
  ensures n == Str2Int(s)
{
  var i := 0;
  n := 0;
  while i < |s|
    invariant i <= |s|
    invariant n == Str2Int(s[0..i])
    decreases |s| - i
  {
    n := n * 2 + (if s[i] == '1' then 1 else 0);
    i := i + 1;
  }
}

method Int2Str_method(n: nat) returns (s: string)
  decreases n
  ensures ValidBitString(s)
  ensures Str2Int(s) == n
{
  if n == 0 then
    s := "0";
  else
    var half_s := Int2Str_method(n / 2);
    var bit := if n % 2 == 1 then '1' else '0';
    s := half_s + [bit];
}

method ModExp_method(x: nat, y: nat, z: nat) returns (n: nat)
  decreases y
  requires z > 1
  ensures n == ModExp_int(x, y, z)
  ensures ModExp_int(x, y, z) == Exp_int(x, y) % z
{
  if y == 0 then
    n := 1 % z;
  else
    var half := ModExp_method(x, y / 2, z);
    var square := (half * half) % z;
    if y % 2 == 1 then
      n := (square * (x % z)) % z;
    else
      n := square;
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
  var x := Str2Int_method(sx);
  var y := Str2Int_method(sy);
  var z := Str2Int_method(sz);
  var res_int := ModExp_method(x, y, z);
  res := Int2Str_method(res_int);
  assert x == Str2Int(sx);
  assert y == Str2Int(sy);
  assert z == Str2Int(sz);
  assert res_int == ModExp_int(x, y, z);
  assert ModExp_int(x, y, z) == Exp_int(x, y) % z;
  assert Str2Int(res) == res_int by { Int2StrStr2Int_ID(res_int); };
}
// </vc-code>

