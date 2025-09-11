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

method DivMod(dividend: string, divisor: string) returns (quotient: string, remainder: string)
  requires ValidBitString(dividend) && ValidBitString(divisor)
  requires Str2Int(divisor) > 0
  ensures ValidBitString(quotient) && ValidBitString(remainder)
  ensures Str2Int(quotient) == Str2Int(dividend) / Str2Int(divisor)
  ensures Str2Int(remainder) == Str2Int(dividend) % Str2Int(divisor)
{
  assume{:axiom} false;
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

// <vc-helpers>
lemma ExpIntProperties(x: nat, y: nat)
  ensures y > 0 ==> Exp_int(x, y) == x * Exp_int(x, y - 1)
  ensures Exp_int(x, 0) == 1
{
}

lemma ModExpProperty(x: nat, y: nat, z: nat)
  requires z > 0
  requires y > 0
  ensures (Exp_int(x, y) % z) == ((x % z) * (Exp_int(x, y - 1) % z)) % z
{
  // Direct calculation without intermediate steps to avoid timeout
  assert Exp_int(x, y) == x * Exp_int(x, y - 1);
}

lemma Str2IntZeroString()
  ensures ValidBitString("0")
  ensures Str2Int("0") == 0
{
}

lemma Str2IntOneString()
  ensures ValidBitString("1")
  ensures Str2Int("1") == 1
{
}

lemma Str2IntAllZeros(s: string)
  requires ValidBitString(s)
  requires forall i | 0 <= i < |s| :: s[i] == '0'
  ensures Str2Int(s) == 0
  decreases |s|
{
  if |s| == 0 {
    // Base case: empty string
  } else {
    // Inductive case
    var prefix := s[0..|s|-1];
    assert forall i | 0 <= i < |prefix| :: prefix[i] == '0';
    Str2IntAllZeros(prefix);
    assert s[|s|-1] == '0';
    assert Str2Int(s) == 2 * Str2Int(prefix) + 0;
    assert Str2Int(s) == 0;
  }
}

lemma Str2IntHasOne(s: string)
  requires ValidBitString(s)
  requires exists i | 0 <= i < |s| :: s[i] == '1'
  ensures Str2Int(s) > 0
  decreases |s|
{
  if |s| == 0 {
    // Contradiction: empty string has no '1'
    assert false;
  } else if s[|s|-1] == '1' {
    // Last bit is 1
    assert Str2Int(s) ==
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
lemma ExpIntProperties(x: nat, y: nat)
  ensures y > 0 ==> Exp_int(x, y) == x * Exp_int(x, y - 1)
  ensures Exp_int(x, 0) == 1
{
}

lemma ModExpProperty(x: nat, y: nat, z: nat)
  requires z > 0
  requires y > 0
  ensures (Exp_int(x, y) % z) == ((x % z) * (Exp_int(x, y - 1) % z)) % z
{
  // Direct calculation without intermediate steps to avoid timeout
  assert Exp_int(x, y) == x * Exp_int(x, y - 1);
}

lemma Str2IntZeroString()
  ensures ValidBitString("0")
  ensures Str2Int("0") == 0
{
}

lemma Str2IntOneString()
  ensures ValidBitString("1")
  ensures Str2Int("1") == 1
{
}

lemma Str2IntAllZeros(s: string)
  requires ValidBitString(s)
  requires forall i | 0 <= i < |s| :: s[i] == '0'
  ensures Str2Int(s) == 0
  decreases |s|
{
  if |s| == 0 {
    // Base case: empty string
  } else {
    // Inductive case
    var prefix := s[0..|s|-1];
    assert forall i | 0 <= i < |prefix| :: prefix[i] == '0';
    Str2IntAllZeros(prefix);
    assert s[|s|-1] == '0';
    assert Str2Int(s) == 2 * Str2Int(prefix) + 0;
    assert Str2Int(s) == 0;
  }
}

lemma Str2IntHasOne(s: string)
  requires ValidBitString(s)
  requires exists i | 0 <= i < |s| :: s[i] == '1'
  ensures Str2Int(s) > 0
  decreases |s|
{
  if |s| == 0 {
    // Contradiction: empty string has no '1'
    assert false;
  } else if s[|s|-1] == '1' {
    // Last bit is 1
    assert Str2Int(s) ==
// </vc-code>

