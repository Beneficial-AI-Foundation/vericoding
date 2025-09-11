ghost function Str2Int(s: string): nat
  requires ValidBitString(s)
  decreases s
{
  if |s| == 0 then  0  else  (2 * Str2Int(s[0..|s|-1]) + (if s[|s|-1] == '1' then 1 else 0))
}
predicate ValidBitString(s: string)
{
  // All characters must be '0' or '1'.
  forall i | 0 <= i < |s| :: s[i] == '0' || s[i] == '1'
}

// <vc-helpers>
function BinOf(n: nat): string
  decreases n
{
  if n == 0 then "" else BinOf(n / 2) + (if n % 2 == 1 then "1" else "0")
}

lemma BinOf_Valid(n: nat)
  ensures ValidBitString(BinOf(n))
  decreases n
{
  if n == 0 {
  } else {
    var q := n / 2;
    var r := n % 2;
    BinOf_Valid(q);
    var tail := if r == 1 then "1" else "0";
    var s := BinOf(q) + tail;
    assert |s| == |BinOf(q)| + 1;
    forall i | 0 <= i < |s|
    {
      if i < |BinOf(q)| {
        assert s[i] == BinOf(q)[i];
        reveal ValidBitString(BinOf(q));
        assert BinOf(q)[i] == '0' || BinOf(q)[i] == '1';
      } else {
        assert s[i] == tail[0];
        if r == 1 {
          assert tail[0] == '1';
        } else {
          assert tail[0] == '0';
        }
        assert s[i] == '0' || s[i] == '1';
      }
    }
  }
}

lemma Str2Int_Push(s: string, i: int)
  requires ValidBitString(s)
  requires 0 <= i < |s|
  ensures Str2Int(s[0..i+1]) == 2 * Str2Int(s[0..i]) + (if s[i] == '1' then 1 else 0)
  decreases i
{
  var t := s[0..i+1];
  // t has length > 0 because i >= 0
  assert |t| > 0;
  // By definition of Str2Int on non-empty string
  assert Str2Int(t) == 2 * Str2Int(t[0..|t|-1]) + (if t[|t|-1] == '1' then 1 else 0);
  // Relate slices
  assert t[0..|t|-1] == s[0..i];
  assert t[|t|-1] == s[i];
  assert (if t[|t|-1] == '1' then 1 else 0) == (if s[i] == '1' then 1 else 0);
  assert Str2Int(t[0..|t|-1]) == Str2Int(s[0..i]);
  // Conclude
  assert Str2Int(s[0..i+1]) == 2 * Str2Int(s[0..i]) + (if s[i] == '1' then 1 else 0);
}

lemma EvenDecomp(n: nat)
  ensures 2 * (n / 2) + (n % 2) == n
  decreases n
{
  var q := n / 2;
  var r := n % 2;
  assert 2 * q + r == n;
}

lemma BinOf_Str2Int(n: nat)
  ensures Str2Int(BinOf(n)) == n
  decreases n
{
  if n == 0 {
  } else {
    var q := n / 2;
    var r := n % 2;
    BinOf_Str2Int(q);
    BinOf_Valid(q);
    var tail := if r == 1 then "1" else "0";
    var s := BinOf(q) + tail;
    assert |s| == |BinOf(q)| + 1;
    var i := |BinOf(q)|;
    assert 0 <= i < |s|;
    if r == 1 {
      assert s[i] == '1';
    } else {
      assert s[i] == '0';
    }
    Str2Int_Push(s, i);
    assert s[0..i] == BinOf(q);
    assert s[0..i+1] == s;
    assert Str2Int(s) == 2 * Str2Int(BinOf(q)) + (if s[i] == '1' then 1 else 0);
    assert Str2Int(s) == 2 * Str2Int(BinOf(q)) + r;
    EvenDecomp(n);
    assert 2 * q + r == n;
    assert Str2Int(s) == n;
  }
}
// </vc-helpers>

// <vc-spec>
method Mul(s1: string, s2: string) returns (res: string)
  requires ValidBitString(s1) && ValidBitString(s2)
  ensures ValidBitString(res)
  ensures Str2Int(res) == Str2Int(s1) * Str2Int(s2)
// </vc-spec>
// <vc-code>
{
  var n1 := Str2Int(s1);
  var n2 := Str2Int(s2);
  var p := n1 * n2;
  res := BinOf(p);
}
// </vc-code>

