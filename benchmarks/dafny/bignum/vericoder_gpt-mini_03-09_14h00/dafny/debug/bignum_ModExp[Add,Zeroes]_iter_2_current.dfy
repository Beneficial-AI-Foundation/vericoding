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
method ParseBits(s: string) returns (v: nat)
  requires ValidBitString(s)
  ensures v == Str2Int(s)
  ensures v < Exp_int(2, |s|)
  decreases |s|
{
  if |s| == 0 {
    v := 0;
  } else {
    var prefix := s[0..|s|-1];
    var pv := ParseBits(prefix);
    var bit := if s[|s|-1] == '1' then 1 else 0;
    v := 2 * pv + bit;
  }
}

method BuildBinary(n: nat, v: nat) returns (s: string)
  requires v < Exp_int(2, n)
  ensures |s| == n
  ensures ValidBitString(s)
  ensures Str2Int(s) == v
  decreases n
{
  if n == 0 {
    s := "";
  } else {
    var low := v % 2;
    var high := v / 2;
    var rest := BuildBinary(n - 1, high);
    s := rest + (if low == 1 then "1" else "0");
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
  var m := ParseBits(sz);
  var origB := ParseBits(sx);
  var origE := ParseBits(sy);

  // modular exponentiation via binary exponentiation
  var resNat := 1 % m;
  var a := origB;
  var e := origE;

  while e > 0
    decreases e
    invariant 0 <= e
    invariant 0 <= resNat < m
    invariant resNat * Exp_int(a, e) % m == Exp_int(origB, origE) % m
  {
    if e % 2 == 1 {
      resNat := resNat * a % m;
      e := e - 1;
    }
    if e > 0 {
      a := a * a % m;
      e := e / 2;
    }
  }

  res := BuildBinary(|sz|, resNat);
}
// </vc-code>

