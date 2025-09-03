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
method StrToNat(s: string) returns (i: nat)
  requires ValidBitString(s)
  ensures i == Str2Int(s)
{
  i := 0;
  var idx := 0;
  while idx < |s|
    decreases |s| - idx
  {
    i := i * 2 + (if s[idx] == '1' then 1 else 0);
    idx := idx + 1;
  }
}

method Pow(x: nat, y: nat) returns (r: nat)
  ensures r == Exp_int(x, y)
{
  r := 1;
  var k := y;
  while k > 0
    decreases k
  {
    r := r * x;
    k := k - 1;
  }
}

method NatToBin(i: nat) returns (s: string)
  ensures ValidBitString(s)
  ensures Str2Int(s) == i
{
  var bits: seq<int> := [];
  var x := i;
  if x == 0 {
    bits := bits + [0];
  } else {
    while x > 0
      decreases x
    {
      bits := bits + [x % 2];
      x := x / 2;
    }
  }

  // Reverse bits to MSB-first order.
  var n := |bits|;
  var rev: seq<int> := [];
  var j := n;
  while j > 0
    decreases j
  {
    rev := rev + [bits[j-1]];
    j := j - 1;
  }

  // Build string by concatenating "0"/"1".
  s := "";
  var idx := 0;
  while idx < |rev|
    decreases |rev| - idx
  {
    s := s + (if rev[idx] == 1 then "1" else "0");
    idx := idx + 1;
  }

  // Prove properties.
  assert forall k | 0 <= k < |s| :: s[k] == '0' || s[k] == '1';
  assert ValidBitString(s);

  var val: nat := 0;
  idx := 0;
  while idx < |s|
    decreases |s| - idx
  {
    val := val * 2 + (if s[idx] == '1' then 1 else 0);
    idx := idx + 1;
  }
  assert val == i;
  assert Str2Int(s) == val;
}

method Zeros_impl(n: nat) returns (s: string)
  ensures |s| == n
  ensures ValidBitString(s)
  ensures Str2Int(s) == 0
  ensures AllZero(s)
{
  s := "";
  var i := 0;
  while i < n
    decreases n - i
  {
    s := s + "0";
    i := i + 1;
  }
  assert |s| == n;
  assert forall k | 0 <= k < |s| :: s[k] == '0';
  assert AllZero(s);
  assert ValidBitString(s);
  var v: nat := 0;
  var idx := 0;
  while idx < |s|
    decreases |s| - idx
  {
    v := v * 2 + (if s[idx] == '1' then 1 else 0);
    idx := idx + 1;
  }
  assert v == 0;
  assert Str2Int(s) == 0;
}

method Add_impl(s1: string, s2: string) returns (res: string)
  requires ValidBitString(s1) && ValidBitString(s2)
  ensures ValidBitString(res)
  ensures Str2Int(res) == Str2Int(s1) + Str2Int(s2)
{
  // Compute integer sum using non-ghost conversion and convert back to binary string.
  var a := StrToNat(s1);
  var b := StrToNat(s2);
  var v := a + b;
  res := NatToBin(v);
  assert ValidBitString(res);
  assert Str2Int(res) == v;
}

method Mul_impl(s1: string, s2: string) returns (res: string)
  requires ValidBitString(s1) && ValidBitString(s2)
  ensures ValidBitString(res)
  ensures Str2Int(res) == Str2Int(s1) * Str2Int(s2)
{
  var a := StrToNat(s1);
  var b := StrToNat(s2);
  var v := a * b;
  res := NatToBin(v);
  assert ValidBitString(res);
  assert Str2Int(res) == v;
}

method ModExpPow2_impl(sx: string, sy: string, n: nat, sz: string) returns (res: string)
  requires ValidBitString(sx) && ValidBitString(sy) &&  ValidBitString(sz)
  requires Str2Int(sy) == Exp_int(2,n) || Str2Int(sy) == 0
  requires |sy| == n+1
  requires Str2Int(sz) > 1
  ensures ValidBitString(res)
  ensures Str2Int(res) == Exp_int(Str2Int(sx), Str2Int(sy)) % Str2Int(sz)
  decreases n
{
  var base := StrToNat(sx);
  var exponent := StrToNat(sy);
  var modulus := StrToNat(sz);
  var p := Pow(base, exponent);
  var v := p % modulus;
  res := NatToBin(v);
  assert ValidBitString(res);
  assert Str2Int(res) == v;
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
  var base := StrToNat(sx);
  var exponent := StrToNat(sy);
  var modulus := StrToNat(sz);
  var p := Pow(base, exponent);
  var v := p % modulus;
  res := NatToBin(v);
}
// </vc-code>

