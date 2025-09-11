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

method Mul(s1: string, s2: string) returns (res: string)
  requires ValidBitString(s1) && ValidBitString(s2)
  ensures ValidBitString(res)
  ensures Str2Int(res) == Str2Int(s1) * Str2Int(s2)
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
function method Nat2Str(v: nat): string
  decreases v
{
  if v == 0 then "" else Nat2Str(v / 2) + (if v % 2 == 1 then "1" else "0")
}

lemma Nat2Str_correct(v: nat)
  ensures ValidBitString(Nat2Str(v))
  ensures Str2Int(Nat2Str(v)) == v
  decreases v
{
  if v == 0 {
    // Nat2Str(0) == "" and Str2Int("") == 0 by definition
  } else {
    Nat2Str_correct(v / 2);
    var s := Nat2Str(v / 2);
    var c := if v % 2 == 1 then "1" else "0";
    // |s + c| > 0
    assert |s + c| > 0;
    // prefix of s+c excluding last char is s
    assert (s + c)[0..|s + c| - 1] == s;
    // last char of s+c is c[0]
    assert (s + c)[|s + c| - 1] == c[0];
    // By definition of Str2Int:
    // Str2Int(s + c) == 2 * Str2Int(s) + (if (s+c)[|s+c|-1] == '1' then 1 else 0)
    assert Str2Int(s + c) == 2 * Str2Int(s) + (if c[0] == '1' then 1 else 0);
    // From induction hypothesis Str2Int(s) == v / 2
    assert Str2Int(s) == v / 2;
    // so Str2Int(s + c) == 2*(v/2) + (v % 2) == v
    assert Str2Int(s + c) == v;
    // ValidBitString: from induction and single char c being '0' or '1'
    assert (c == "0" || c == "1");
    // prove ValidBitString(s + c)
    // For any index j in range of s+c:
    // if j < |s| then s[j] is '0' or '1' by induction
    // else j == |s| and (s+c)[j] == c[0] which is '0' or '1'
    assert ValidBitString(s + c);
  }
}

function method Exp_int_m(x: nat, y: nat): nat
  decreases y
{
  if y == 0 then 1 else x * Exp_int_m(x, y - 1)
}

lemma Exp_int_equiv(x: nat, y: nat)
  ensures Exp_int_m(x, y) == Exp_int(x, y)
  decreases y
{
  if y == 0 {
    // both equal 1
  } else {
    Exp_int_equiv(x, y - 1);
    // unfold both definitions: Exp_int_m(x,y) = x * Exp_int_m(x,y-1)
    // and Exp_int(x,y) = x * Exp_int(x,y-1)
    // equality follows from recursive call
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
  // Parse sx into x
  var x := 0;
  var i := 0;
  while i < |sx|
    invariant 0 <= i <= |sx|
    invariant x == Str2Int(sx[0..i])
  {
    var b := if sx[i] == '1' then 1 else 0;
    x := 2 * x + b;
    i := i + 1;
  }

  // Parse sy into y
  var y := 0;
  i := 0;
  while i < |sy|
    invariant 0 <= i <= |sy|
    invariant y == Str2Int(sy[0..i])
  {
    var b := if sy[i] == '1' then 1 else 0;
    y := 2 * y + b;
    i := i + 1;
  }

  // Parse sz into m
  var m := 0;
  i := 0;
  while i < |sz|
    invariant 0 <= i <= |sz|
    invariant m == Str2Int(sz[0..i])
  {
    var b := if sz[i] == '1' then 1 else 0;
    m := 2 * m + b;
    i := i + 1;
  }

  // Compute value v = Exp_int_m(x,y) % m
  // m > 1 by precondition, so modulus is well-defined
  var v := Exp_int_m(x, y) % m;

  // Convert v to bitstring
  res := Nat2Str(v);

  // Prove postconditions by chaining equalities/lemmas
  Nat2Str_correct(v);
  Exp_int_equiv(x, y);
  // x == Str2Int(sx), y == Str2Int(sy), m == Str2Int(sz) from parsing invariants
  // hence Str2Int(res) == Exp_int(Str2Int(sx), Str2Int(sy)) % Str2Int(sz)
  return;
}
// </vc-code>

