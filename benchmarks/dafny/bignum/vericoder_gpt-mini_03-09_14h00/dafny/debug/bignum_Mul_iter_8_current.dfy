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
    // BinOf(0) == "" which trivially satisfies ValidBitString
  } else {
    var q := n / 2;
    var r := n % 2;
    BinOf_Valid(q);
    var tail := if r == 1 then "1" else "0";
    var s := BinOf(q) + tail;
    // show ValidBitString(s)
    assert |s| == |BinOf(q)| + 1;
    forall i | 0 <= i < |s|
    {
      if i < |BinOf(q)| {
        assert s[i] == BinOf(q)[i];
        reveal ValidBitString(BinOf(q));
        assert BinOf(q)[i] == '0' || BinOf(q)[i] == '1';
      } else {
        // i == |BinOf(q)|
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

lemma BinOf_Str2Int(n: nat)
  ensures Str2Int(BinOf(n)) == n
  decreases n
{
  if n == 0 {
    // Str2Int("") == 0 by definition
  } else {
    var q := n / 2;
    var r := n % 2;
    BinOf_Str2Int(q);
    BinOf_Valid(q);
    var tail := if r == 1 then "1" else "0";
    var s := BinOf(q) + tail;
    assert |s| == |BinOf(q)| + 1;
    var i := |BinOf(q)|;
    // Preconditions for Str2Int_Push: ValidBitString(s) and 0 <= i < |s|
    assert 0 <= i < |s|;
    // Show s[i] corresponds to r
    if r == 1 {
      assert s[i] == '1';
    } else {
      assert s[i] == '0';
    }
    // Apply Str2Int_Push to get Str2Int(s[0..i+1]) == 2*Str2Int(s[0..i]) + (if s[i]=='1' then 1 else 0)
    Str2Int_Push(s, i);
    // s[0..i] == BinOf(q) and s[0..i+1] == s
    assert s[0..i] == BinOf(q);
    assert s[0..i+1] == s;
    // Thus Str2Int(s) == 2*Str2Int(BinOf(q)) + r
    assert Str2Int(s) == 2 * Str2Int(BinOf(q)) + (if s[i] == '1' then 1 else 0);
    // By induction Str2Int(BinOf(q)) == q
    assert Str2Int(s) == 2 * q + r;
    // Use EvenDecomp to conclude equality with n
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

