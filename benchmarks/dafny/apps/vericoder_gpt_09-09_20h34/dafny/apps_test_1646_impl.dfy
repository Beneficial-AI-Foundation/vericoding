predicate ValidBinaryString(s: string)
{
    |s| > 0 && 
    (forall i :: 0 <= i < |s| ==> s[i] == '0' || s[i] == '1') &&
    (s == "0" || s[0] == '1')
}

function count_zeros(s: string): int
    ensures count_zeros(s) >= 0
    ensures count_zeros(s) <= |s|
{
    if |s| == 0 then 0
    else (if s[0] == '0' then 1 else 0) + count_zeros(s[1..])
}

predicate IsMinimalForm(s: string, result: string)
{
    s == "0" ==> result == "0"
    &&
    s != "0" ==> result == "1" + seq(count_zeros(s), _ => '0')
}

// <vc-helpers>
lemma ValidBinaryString_Zero()
  ensures ValidBinaryString("0")
{
  assert |"0"| == 1;
  assert |"0"| > 0;

  assert {:trigger "0"[i]} forall i :: 0 <= i < |"0"| ==> "0"[i] == '0' || "0"[i] == '1' by {
    if 0 <= i && i < |"0"| {
      assert i == 0;
      assert "0"[i] == '0';
    }
  };

  assert "0" == "0" || "0"[0] == '1';
}

lemma ValidBinaryString_ConcatOneZeros(n: int)
  requires n >= 0
  ensures ValidBinaryString("1" + seq(n, _ => '0'))
{
  var z := seq(n, _ => '0');
  var r := "1" + z;

  assert |r| == |"1"| + |z|;
  assert |r| > 0;

  assert {:trigger r[i]} forall i :: 0 <= i < |r| ==> r[i] == '0' || r[i] == '1' by {
    if 0 <= i && i < |r| {
      if i == 0 {
        assert r[i] == "1"[0];
        assert r[i] == '1';
      } else {
        assert i > 0;
        assert i < 1 + |z|;
        assert 0 <= i - 1 < |z|;
        assert r[i] == z[i - 1];
        assert r[i] == '0';
      }
    }
  };

  assert r[0] == '1';
}
// </vc-helpers>

// <vc-spec>
method solve(n: int, s: string) returns (result: string)
    requires n >= 1 && n <= 100
    requires |s| == n
    requires ValidBinaryString(s)
    ensures ValidBinaryString(result)
    ensures IsMinimalForm(s, result)
// </vc-spec>
// <vc-code>
{
  if s == "0" {
    result := "0";
    ValidBinaryString_Zero();
  } else {
    var k := count_zeros(s);
    result := "1" + seq(k, _ => '0');
    ValidBinaryString_ConcatOneZeros(k);
  }
}
// </vc-code>

