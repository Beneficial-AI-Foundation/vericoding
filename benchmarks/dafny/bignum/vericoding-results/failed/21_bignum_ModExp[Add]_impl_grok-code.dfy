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

// <vc-helpers>
function Str2IntImpl(s: string): nat
  requires ValidBitString(s)
  decreases s
{
  if |s| == 0 then 0 else (2 * Str2IntImpl(s[0..|s|-1]) + (if s[|s|-1] == '1' then 1 else 0))
}

function Exp_intimp(x: nat, y:nat): nat
{
  if y == 0 then 1 else x * Exp_intimp(x, y - 1)
}

function IntToBitsRec(n: nat, acc: seq<int>): seq<int>
  requires n > 0
  decreases n
{
  if n == 1 then [1] + acc
  else if n % 2 == 0 then IntToBitsRec(n/2, [0] + acc)
  else IntToBitsRec(n/2, [1] + acc)
}

function IntToBits(n: nat): seq<int>
{
  if n == 0 then [0] else IntToBitsRec(n, [])
}

function Str2IntSeq(s: seq<int>): nat
  requires forall i :: 0 <= i < |s| ==> s[i] == 0 || s[i] == 1
  decreases |s|
{
  if |s| == 0 then 0 else s[0] * Exp_intimp(2, |s|-1) + Str2IntSeq(s[1..])
}

function StringFromSeq(s: seq<int>): string
  decreases |s|
  ensures |StringFromSeq(s)| == |s|
  ensures ValidBitString(StringFromSeq(s))
{
  if s == [] then ""
  else StringFromSeq(s[..|s|-1]) + (if s[|s|-1] == 0 then "0" else "1")
}

function IntToStr(n: nat): string
  ensures ValidBitString(IntToStr(n)) && Str2IntImpl(IntToStr(n)) == n
{
  if n == 0 then "0"
  else if n % 2 == 0 then IntToStr(n/2) + "0"
  else IntToStr(n/2) + "1"
}

function ModExpNum(x: nat, y: nat, z: nat): nat
  requires z > 1
  decreases y
{
  if y == 0 then 1 % z
  else if y % 2 == 0 then ((ModExpNum(x, y / 2, z) * ModExpNum(x, y / 2, z)) % z)
  else ((x % z * ModExpNum(x, y - 1, z)) % z)
}

lemma ExpModExp(x: nat, y: nat, z: nat)
  requires z > 1
  ensures ModExpNum(x, y, z) == Exp_int(x, y) % z
  decreases y
{
  if y == 0 {
  } else if y % 2 == 0 {
    calc {
      ModExpNum(x, y, z);
      == ((ModExpNum(x, y / 2, z) * ModExpNum(x, y / 2, z)) % z);
      { ExpModExp(x, y / 2, z); }
      == ((Exp_int(x, y / 2) % z * Exp_int(x, y / 2) % z) % z);
      == (((Exp_int(x, y / 2) * Exp_int(x, y / 2)) % z) % z);
      == (Exp_int(x, y) % z) % z;
      == Exp_int(x, y) % z;
    }
  } else {
    calc {
      ModExpNum(x, y, z);
      == ((x % z * ModExpNum(x, y - 1, z)) % z);
      { ExpModExp(x, y - 1, z); }
      == ((x % z * (Exp_int(x, y - 1) % z)) % z);
      == ((x * Exp_int(x, y - 1)) % z) % z;
      == (Exp_int(x, y) % z) % z;
      == Exp_int(x, y) % z;
    }
  }
}

lemma Str2IntEq(s: string)
  requires ValidBitString(s)
  ensures Str2Int(s) == Str2IntImpl(s)
  decreases |s|
{
  if |s| == 0 {
  } else {
    Str2IntEq(s[0..|s|-1]);
  }
}

lemma Exp_intEq(x: nat, y: nat)
  ensures Exp_int(x, y) == Exp_intimp(x, y)
  decreases y
{
  if y == 0 {
  } else {
    Exp_intEq(x, y-1);
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
  var x : nat := Str2IntImpl(sx);
  var y : nat := Str2IntImpl(sy);
  var z : nat := Str2IntImpl(sz);
  Str2IntEq(sx);
  Str2IntEq(sy);
  Str2IntEq(sz);
  var num_res : nat := ModExpNum(x, y, z);
  ExpModExp(x, y, z);
  res := IntToStr(num_res);
  Str2IntEq(res);
}
// </vc-code>

