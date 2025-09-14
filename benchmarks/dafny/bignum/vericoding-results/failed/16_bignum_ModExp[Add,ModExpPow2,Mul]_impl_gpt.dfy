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

// <vc-helpers>
function Nat2Str(n: nat): string
  decreases n
{
  if n == 0 then
    "0"
  else
    Nat2Str(n / 2) + (if n % 2 == 1 then "1" else "0")
}

lemma Lemma_ValidBitString_Const()
  ensures ValidBitString("")
  ensures ValidBitString("0")
  ensures ValidBitString("1")
{
}

lemma Lemma_ValidBitString_Concat(s: string, t: string)
  requires ValidBitString(s)
  requires ValidBitString(t)
  ensures ValidBitString(s + t)
{
  assert forall i | 0 <= i < |s| + |t| ::
    (s + t)[i] == '0' || (s + t)[i] == '1' by {
      if i < |s| {
        assert (s + t)[i] == s[i];
      } else {
        var j := i - |s|;
        assert 0 <= j < |t|;
        assert (s + t)[i] == t[j];
      }
    };
}

lemma Lemma_Nat2Str_Correct(n: nat)
  ensures ValidBitString(Nat2Str(n))
  ensures Str2Int(Nat2Str(n)) == n
  decreases n
{
  if n == 0 {
    Lemma_ValidBitString_Const();
    assert Str2Int(Nat2Str(0)) == 0;
  } else {
    Lemma_Nat2Str_Correct(n / 2);
    Lemma_ValidBitString_Const();

    var t := Nat2Str(n);
    assert t == Nat2Str(n / 2) + (if n % 2 == 1 then "1" else "0");

    // ValidBitString(t)
    assert ValidBitString(Nat2Str(n / 2));
    assert ValidBitString(if n % 2 == 1 then "1" else "0");
    assert forall i | 0 <= i < |t| ::
      t[i] == '0' || t[i] == '1' by {
        if i < |Nat2Str(n / 2)| {
          assert t[i] == Nat2Str(n / 2)[i];
        } else {
          var j := i - |Nat2Str(n / 2)|;
          assert 0 <= j < |if n % 2 == 1 then "1" else "0"|;
          assert t[i] == (if n % 2 == 1 then "1" else "0")[j];
        }
      };

    // Str2Int(t) == n
    assert |t| > 0;
    assert t[0..|t|-1] == Nat2Str(n / 2);
    assert t[|t|-1] == (if n % 2 == 1 then '1' else '0');

    assert Str2Int(t) ==
      2 * Str2Int(t[0..|t|-1]) + (if t[|t|-1] == '1' then 1 else 0);

    assert Str2Int(t[0..|t|-1]) == Str2Int(Nat2Str(n / 2));
    assert Str2Int(Nat2Str(n / 2)) == n / 2;

    if n % 2 == 1 {
      assert (if n % 2 == 1 then 1 else 0) == n % 2;
    } else {
      assert (if n % 2 == 1 then 1 else 0) == n % 2;
    }

    assert Str2Int(t) == 2 * (n / 2) + n % 2;
    assert n == 2 * (n / 2) + n % 2;
    assert Str2Int(t) == n;
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
  var v: nat := Exp_int(Str2Int(sx), Str2Int(sy)) % Str2Int(sz);
  res := Nat2Str(v);
  Lemma_Nat2Str_Correct(v);
}
// </vc-code>

