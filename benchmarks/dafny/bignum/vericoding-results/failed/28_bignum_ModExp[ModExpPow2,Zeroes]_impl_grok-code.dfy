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

method Zeros(n: nat) returns (s: string)
  ensures |s| == n
  ensures ValidBitString(s)
  ensures Str2Int(s) == 0
  ensures AllZero(s)
{
  assume{:axiom} false;
}

// <vc-helpers>
function Str2Int(s: string): nat
  requires ValidBitString(s)
  decreases |s|
{
  if |s| == 0 then 0 else 2 * Str2Int(s[0..|s|-1]) + (if s[|s|-1] == '1' then 1 else 0)
}
function Exp_int(x: nat, y: nat): nat
{
  if y == 0 then 1 else x * Exp_int(x, y - 1)
}
predicate ValidBitString(s: string)
{
  forall i | 0 <= i < |s| :: s[i] == '0' || s[i] == '1'
}
predicate AllZero(s: string)
{
  forall i | 0 <= i < |s| :: s[i] == '0'
}
function Int2Str_aux(v: nat): string
  decreases v
{
  if v == 0 then "" 
  else Int2Str_aux(v / 2) + if v % 2 == 1 then "1" else "0"
}

function Int2Str(v: nat): string
{
  if v == 0 then "0" 
  else Int2Str_aux(v)
}

lemma Str_inverse(v: nat)
  ensures ValidBitString(Int2Str(v)) && Str2Int(Int2Str(v)) == v
{
  if v == 0 {
  } else {
    Str_inverse(v / 2);
    var s1 := Int2Str_aux(v / 2);
    assert ValidBitString(s1) && Str2Int(s1) == v / 2;
    var s2 := s1 + if v % 2 == 1 then "1" else "0";
    assert ValidBitString(s2);
    assert Str2Int(s2) == 2 * Str2Int(s1) + if v % 2 == 1 then 1 else 0;
    assert v == 2 * (v / 2) + if v % 2 == 1 then 1 else 0;
  }
}

method ModPow(x: nat, y: nat, m: nat) returns (res: nat)
  requires m > 1
  ensures res == Exp_int(x, y) % m
  decreases y
{
  if y == 0 {
    res := 1;
  } else if y % 2 == 1 {
    var rec := ModPow(x, y - 1, m);
    res := (rec * x) % m;
  } else {
    var rec := ModPow(x, y / 2, m);
    var sq := (rec * rec) % m;
    res := sq;
  }
}

method ModExpPow2(sx: string, sy: string, n: nat, sz: string) returns (res: string)
  requires ValidBitString(sx) && ValidBitString(sy) &&  ValidBitString(sz)
  requires Str2Int(sy) == Exp_int(2,n) || Str2Int(sy) == 0
  requires |sy| == n+1
  requires Str2Int(sz) > 1
  ensures ValidBitString(res)
  ensures Str2Int(res) == Exp_int(Str2Int(sx), Str2Int(sy)) % Str2Int(sz)
{
  var x := Str2Int(sx);
  var y := Str2Int(sy);
  var m := Str2Int(sz);
  if y == 0 {
    var one_mod := 1 % m;
    res := Int2Str(one_mod);
    Str_inverse(one_mod);
  } else {
    var base := x % m;
    var pow := ModPow(base, n, m);
    res := Int2Str(pow);
    Str_inverse(pow);
  }
}

method Zeros(n: nat) returns (s: string)
  ensures |s| == n
  ensures ValidBitString(s)
  ensures Str2Int(s) == 0
  ensures AllZero(s)
{
  s := "";
  var i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant |s| == i
    invariant ValidBitString(s)
    invariant AllZero(s)
    invariant Str2Int(s) == 0
  {
    s := s + "0";
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
  var x := Str2Int(sx);
  var y := Str2Int(sy);
  var m := Str2Int(sz);
  var pow := ModPow(x, y, m);
  res := Int2Str(pow);
  Str_inverse(pow);
}
// </vc-code>

