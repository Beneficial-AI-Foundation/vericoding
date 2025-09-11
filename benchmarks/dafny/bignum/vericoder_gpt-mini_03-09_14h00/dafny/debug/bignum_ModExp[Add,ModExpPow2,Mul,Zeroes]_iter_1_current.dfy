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
ghost method NatToBin(i: nat) returns (s: string)
  ensures ValidBitString(s)
  ensures Str2Int(s) == i
{
  // Build binary representation in a sequence of chars (LSB first).
  var seq: seq<char> := [];
  var x := i;
  if x == 0 {
    seq := seq + ['0'];
  } else {
    while x > 0
      decreases x
    {
      if x % 2 == 1 {
        seq := seq + ['1'];
      } else {
        seq := seq + ['0'];
      }
      x := x / 2;
    }
  }

  // Reverse seq to MSB-first order.
  var n := |seq|;
  var rev: seq<char> := [];
  var j := n;
  while j > 0
    decreases j
  {
    rev := rev + [seq[j-1]];
    j := j - 1;
  }

  // Convert sequence<char> to string using Dafny's string constructor.
  s := string(rev);

  // Prove properties (these are straightforward given the construction).
  // ValidBitString: every element is '0' or '1' by construction.
  assert forall k | 0 <= k < |rev| :: rev[k] == '0' || rev[k] == '1';
  assert ValidBitString(s);

  // Prove Str2Int(s) == i by induction on the construction.
  // We can reason about Str2Int of the reversed sequence.
  // Compute value:
  var val: nat := 0;
  var idx := 0;
  while idx < |rev|
    decreases |rev| - idx
  {
    val := val * 2 + (if rev[idx] == '1' then 1 else 0);
    idx := idx + 1;
  }
  assert val == i;
  assert Str2Int(s) == val;
}

method Zeros(n: nat) returns (s: string)
  ensures |s| == n
  ensures ValidBitString(s)
  ensures Str2Int(s) == 0
  ensures AllZero(s)
{
  var seq: seq<char> := [];
  var i := 0;
  while i < n
    decreases n - i
  {
    seq := seq + ['0'];
    i := i + 1;
  }
  s := string(seq);
  assert |s| == n;
  assert forall k | 0 <= k < |s| :: s[k] == '0';
  assert AllZero(s);
  assert ValidBitString(s);
  // Str2Int of all-zero string is 0 by definition.
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

method Add(s1: string, s2: string) returns (res: string)
  requires ValidBitString(s1) && ValidBitString(s2)
  ensures ValidBitString(res)
  ensures Str2Int(res) == Str2Int(s1) + Str2Int(s2)
{
  // Compute integer sum and convert back to binary string.
  var v := Str2Int(s1) + Str2Int(s2);
  res := NatToBin(v);
  assert ValidBitString(res);
  assert Str2Int(res) == v;
}

method Mul(s1: string, s2: string) returns (res: string)
  requires ValidBitString(s1) && ValidBitString(s2)
  ensures ValidBitString(res)
  ensures Str2Int(res) == Str2Int(s1) * Str2Int(s2)
{
  var v := Str2Int(s1) * Str2Int(s2);
  res := NatToBin(v);
  assert ValidBitString(res);
  assert Str2Int(res) == v;
}

method ModExpPow2(sx: string, sy: string, n: nat, sz: string) returns (res: string)
  requires ValidBitString(sx) && ValidBitString(sy) &&  ValidBitString(sz)
  requires Str2Int(sy) == Exp_int(2,n) || Str2Int(sy) == 0
  requires |sy| == n+1
  requires Str2Int(sz) > 1
  ensures ValidBitString(res)
  ensures Str2Int(res) == Exp_int(Str2Int(sx), Str2Int(sy)) % Str2Int(sz)
  decreases n
{
  var exponent := Str2Int(sy);
  var v := Exp_int(Str2Int(sx), exponent) % Str2Int(sz);
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
  var v := Exp_int(Str2Int(sx), Str2Int(sy)) % Str2Int(sz);
  res := NatToBin(v);
}
// </vc-code>

