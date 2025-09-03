ghost function Exp_int(x: nat, y:nat): nat
{
  if y == 0 then 1 else x * Exp_int(x, y - 1)
}
predicate ValidBitString(s: string)
{
  // All characters must be '0' or '1'.
  forall i | 0 <= i < |s| :: s[i] == '0' || s[i] == '1'
}
ghost function Str2Int(s: string): nat
  requires ValidBitString(s)
  decreases s
{
  if |s| == 0 then  0  else  (2 * Str2Int(s[0..|s|-1]) + (if s[|s|-1] == '1' then 1 else 0))
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
function Int2Str(n: nat): string
  ensures ValidBitString(Int2Str(n))
  ensures Str2Int(Int2Str(n)) == n
  decreases n
{
  if n == 0 then "" else Int2Str(n / 2) + (if n % 2 == 1 then "1" else "0")
}

function ParseBits(s: string): nat
  requires ValidBitString(s)
  decreases s
{
  if |s| == 0 then 0 else 2 * ParseBits(s[0..|s|-1]) + (if s[|s|-1] == '1' then 1 else 0)
}

lemma ParseBitsEqualsStr2Int(s: string)
  requires ValidBitString(s)
  ensures ParseBits(s) == Str2Int(s)
  decreases s
{
  if |s| > 0 {
    ParseBitsEqualsStr2Int(s[0..|s|-1]);
  }
}

lemma Exp_succ(x: nat, y: nat)
  ensures Exp_int(x, y + 1) == x * Exp_int(x, y)
  decreases y
{
  if y > 0 {
    Exp_succ(x, y - 1);
  }
}

lemma Exp_add(x: nat, a: nat, b: nat)
  ensures Exp_int(x, a + b) == Exp_int(x, a) * Exp_int(x, b)
  decreases b
{
  if b > 0 {
    Exp_add(x, a, b - 1);
  }
}
// </vc-helpers>

// <vc-spec>
method ModExpPow2(sx: string, sy: string, n: nat, sz: string) returns (res: string)
  requires ValidBitString(sx) && ValidBitString(sy) &&  ValidBitString(sz)
  // sy is power of 2 or zero
  requires Str2Int(sy) == Exp_int(2,n) || Str2Int(sy) == 0
  requires |sy| == n+1
  requires Str2Int(sz) > 1
  ensures ValidBitString(res)
  ensures Str2Int(res) == Exp_int(Str2Int(sx), Str2Int(sy)) % Str2Int(sz)
  decreases n
// </vc-spec>
// <vc-code>
{
  var vx := ParseBits(sx);
  var vy := ParseBits(sy);
  var m := ParseBits(sz);
  ghost ParseBitsEqualsStr2Int(sx);
  ghost ParseBitsEqualsStr2Int(sy);
  ghost ParseBitsEqualsStr2Int(sz);
  var resultNat: nat;
  if vy == 0 {
    resultNat := 1 % m;
  } else {
    var cur := vx % m;
    var i := 0;
    while i < n
      invariant 0 <= i <= n
      invariant cur < m
      invariant cur == Exp_int(vx, Exp_int(2, i)) % m
      decreases n - i
    {
      ghost Exp_succ(2, i);
      ghost Exp_add(vx, Exp_int(2, i), Exp_int(2, i));
      cur := (cur * cur) % m;
      i := i + 1;
    }
    resultNat := cur;
  }
  res := Int2Str(resultNat);
  assert Str2Int(res) == resultNat;
  if vy == 0 {
    assert Exp_int(vx, vy) == 1;
    assert Exp_int(vx, vy) % m == resultNat;
  } else {
    assert vy == Exp_int(2, n);
    assert resultNat == Exp_int(vx, Exp_int(2, n)) % m;
    assert Exp_int(vx, vy) == Exp_int(vx, Exp_int(2, n));
    assert Exp_int(vx, vy) % m == resultNat;
  }
}
// </vc-code>

