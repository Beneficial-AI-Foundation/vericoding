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
ghost function Nat2Str(n: nat): string
  decreases n
{
  if n == 0 then "" else
    var q := n / 2;
    var bit := if n % 2 == 1 then "1" else "0";
    Nat2Str(q) + bit
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
    // Let b = b0 + c where c is last char
    var bprefix := b[0..|b|-1];
    var last := b[|b|-1];
    // By induction on bprefix
    StrConcatLemma(a, bprefix);
    // Str2Int((a + bprefix) + [last]) = 2 * Str2Int(a + bprefix) + (if last=='1' then 1 else 0)
    // Use definition of Str2Int on non-empty string
    // Now expand Str2Int(a + bprefix) by IH and simplify
  }
}

lemma SingleCharStrVal(s: string, i: int)
  requires 0 <= i < |s|
  requires s[i] == '0' || s[i] == '1'
  ensures Str2Int(s[i..i+1]) == (if s[i] == '1' then 1 else 0)
{
  // By definition of Str2Int for length-1 string
}

lemma Nat2Str_correct(n: nat)
  ensures ValidBitString(Nat2Str(n)) && Str2Int(Nat2Str(n)) == n
  decreases n
{
  if n == 0 {
    // Nat2Str(0) == "" and Str2Int("") == 0 by definition
  } else {
    var q := n / 2;
    var r := n % 2;
    Nat2Str_correct(q);
    // Let bit be "1" if r==1 else "0"
    // Nat2Str(n) = Nat2Str(q) + bit
    // By StrConcatLemma and properties of division: Str2Int(Nat2Str(n)) = Str2Int(Nat2Str(q)) * 2 + r = q*2 + r = n
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
    // resInt := (resInt * resInt) % m;
    var tmp := (resInt * resInt) % m;
    // By ExpAdd, Exp_int(x, prefixVal + prefixVal) == Exp_int(x, prefixVal) * Exp_int(x, prefixVal)
    ExpAdd(x, prefixVal, prefixVal);
    // Now tmp corresponds to Exp_int(x, 2*prefixVal) % m
    resInt := tmp;
    if sy[i] == '1' {
      resInt := (resInt * x) % m;
    }
    // Now need to show updated resInt == Exp_int(x, Str2Int(sy[0..i+1])) % m
    // Use StrConcatLemma for a = sy[0..i], b = sy[i..i+1] (effectively shows Str2Int(sy[0..i+1]) = 2*prefixVal + bit)
    StrConcatLemma(sy[0..i], sy[i..i+1]);
    // Also single char value
    SingleCharStrVal(sy, i);
    i := i + 1;
  }
  // At loop exit i == |sy|, so resInt == Exp_int(x, Str2Int(sy)) % m
  res := Nat2Str(resInt);
  // Postconditions follow from Nat2Str_correct
  Nat2Str_correct(resInt);
}
// </vc-code>

