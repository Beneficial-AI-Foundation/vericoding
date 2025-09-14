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
  decreases n
{
  if n == 0 then "" else Int2Str(n / 2) + (if n % 2 == 1 then "1" else "0")
}

function ExpMod(x: nat, y: nat, z: nat): nat
  requires z > 1
  decreases y
{
  if y == 0 then 1 else ((x * ExpMod(x, y-1, z)) % z)
}

lemma Int2StrCorrect(n: nat)
  ensures ValidBitString(Int2Str(n)) && Str2Int(Int2Str(n)) == n
  decreases n
{
  if n ==0 {
    assert ValidBitString("") ;
  } else {
    Int2StrCorrect(n/2);
    var s2 := if n %2 ==1 then "1" else "0";
    var s1 := Int2Str(n/2);
    assert ValidBitString(s1) && Str2Int(s1) == n/2;
    assert ValidBitString(s2) ;
    assert ValidBitString(s1 + s2);
    assert Str2Int(s1 + s2) == 2 * Str2Int(s1) + (if s2 == "1" then 1 else 0);
    assert n / 2 * 2 + (if s2 == "1" then 1 else 0) == n;
  }
}

lemma Int2StrValid(n: nat)
  ensures ValidBitString(Int2Str(n))
  decreases n
{
  if n != 0 {
    Int2StrValid(n / 2);
    var s1 := Int2Str(n/2);
    var s2 := if n %2 ==1 then "1" else "0";
    assert ValidBitString(s1);
    assert ValidBitString(s2);
    assert ValidBitString(s1 + s2);
  }
}

function BinStr2Nat(s: string): nat
  requires ValidBitString(s)
  decreases |s|
{
  if |s| == 0 then 0 else 2 * BinStr2Nat(s[0..|s|-1]) + (if s[|s|-1] == '1' then 1 else 0)
}

lemma BinStr2NatCorrect(s: string)
  requires ValidBitString(s)
  ensures BinStr2Nat(s) == Str2Int(s)
  decreases |s|
{
  if |s| != 0 {
    BinStr2NatCorrect(s[0..|s|-1]);
  }
}

lemma ExpModCorrect(x: nat, y: nat, z: nat)
  requires z > 1
  ensures ExpMod(x, y, z) == Exp_int(x, y) % z
  decreases y
{
  if y != 0 {
    ExpModCorrect(x, y-1, z);
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
  var x := BinStr2Nat(sx);
  var y := BinStr2Nat(sy);
  var z := BinStr2Nat(sz);
  BinStr2NatCorrect(sz);
  assert z > 1;
  res := Int2Str(ExpMod(x, y, z));
  BinStr2NatCorrect(sx);
  BinStr2NatCorrect(sy);
  ExpModCorrect(x, y, z);
  Int2StrValid(ExpMod(x, y, z));
  Int2StrCorrect(ExpMod(x, y, z));
}
// </vc-code>

