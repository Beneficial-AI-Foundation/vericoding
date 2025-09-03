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

method Mul(s1: string, s2: string) returns (res: string)
  requires ValidBitString(s1) && ValidBitString(s2)
  ensures ValidBitString(res)
  ensures Str2Int(res) == Str2Int(s1) * Str2Int(s2)
{
  assume{:axiom} false;
}

// <vc-helpers>
function method Nat2Str(n: nat): string
  decreases n
{
  if n == 0 then "" else Nat2Str(n / 2) + (if n % 2 == 1 then "1" else "0")
}

lemma ExpAdd(x: nat, a: nat, b: nat)
  ensures Exp_int(x, a + b) == Exp_int(x, a) * Exp_int(x, b)
  decreases b
{
  if b == 0 {
  } else {
    ExpAdd(x, a, b - 1);
    // Exp_int(x, a + b) = x * Exp_int(x, a + b - 1)
    // = x * (Exp_int(x, a) * Exp_int(x, b - 1)) = Exp_int(x, a) * Exp_int(x, b)
  }
}

lemma Exp2_mult(n: nat)
  ensures Exp_int(2, n + 1) == 2 * Exp_int(2, n)
{
  // Follows from ExpAdd(2, n, 1)
  ExpAdd(2, n, 1);
}

lemma StrConcatLemma(a: string, b: string)
  ensures Str2Int(a + b) == Str2Int(a) * Exp_int(2, |b|) + Str2Int(b)
  decreases |b|
{
  if |b| == 0 {
  } else {
    var bprefix := b[0..|b|-1];
    var last := b[|b|-1];
    StrConcatLemma(a, bprefix);
  }
}

lemma SingleCharStrVal(s: string, i: int)
  requires 0 <= i < |s|
  requires s[i] == '0' || s[i] == '1'
  ensures Str2Int(s[i..i+1]) == (if s[i] == '1' then 1 else 0)
{
}

lemma Nat2Str_correct(n: nat)
  ensures ValidBitString(Nat2Str(n)) && Str2Int(Nat2Str(n)) == n
  decreases n
{
  if n == 0 {
  } else {
    var q := n / 2;
    var r := n % 2;
    Nat2Str_correct(q);
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
  var m := Str2Int(sz);
  var resInt := 1 % m;
  var i := 0;
  // Invariant: 0 <= i <= |sy|, 0 <= resInt < m, and resInt == Exp_int(x, Str2Int(sy[0..i])) % m
  while i < |sy|
    invariant 0 <= i <= |sy|
    invariant 0 <= resInt < m
    invariant resInt == Exp_int(x, Str2Int(sy[0..i])) % m
    decreases |sy| - i
  {
    var prefixVal := Str2Int(sy[0..i]);
    // square
    var tmp := (resInt * resInt) % m;
    ExpAdd(x, prefixVal, prefixVal);
    resInt := tmp;
    if sy[i] == '1' {
      resInt := (resInt * x) % m;
    }
    StrConcatLemma(sy[0..i], sy[i..i+1]);
    SingleCharStrVal(sy, i);
    i := i + 1;
  }
  res := Nat2Str(resInt);
  Nat2Str_correct(resInt);
}
// </vc-code>

