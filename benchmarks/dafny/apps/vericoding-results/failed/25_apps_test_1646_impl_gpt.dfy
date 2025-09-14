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
lemma ValidBinaryStringOfZero()
    ensures ValidBinaryString("0")
{
    assert |"0"| == 1;
    assert |"0"| > 0;

    assert (forall i {:trigger "0"[i]} :: 0 <= i < |"0"| ==> "0"[i] == '0' || "0"[i] == '1')
      by {
        forall i | 0 <= i < |"0"| {
          assert i == 0;
          assert "0"[i] == '0';
        }
      }

    assert "0" == "0" || "0"[0] == '1';
    assert ValidBinaryString("0");
}

lemma ValidBinaryStringOfOneZeros(k: nat)
    ensures ValidBinaryString("1" + seq(k, _ => '0'))
{
    var zeros := seq(k, _ => '0');
    var r := "1" + zeros;

    assert |"1"| == 1;
    assert |zeros| == k;
    assert |r| == |"1"| + |zeros|;
    assert |r| == 1 + k;
    assert |r| > 0;

    assert (forall i {:trigger r[i]} :: 0 <= i < |r| ==> r[i] == '0' || r[i] == '1')
      by {
        forall i | 0 <= i < |r| {
          if i < 1 {
            assert i == 0;
            assert r[i] == "1"[i];
            assert r[i] == '1';
          } else {
            assert 1 <= i;
            assert 0 <= i - 1;
            assert i < 1 + k;
            assert i - 1 < k;
            assert r[i] == zeros[i - 1];
            assert zeros[i - 1] == '0';
          }
        }
      }

    assert r[0] == "1"[0];
    assert r[0] == '1';

    assert r == "0" || r[0] == '1';
    assert ValidBinaryString(r);
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
    ValidBinaryStringOfZero();
    assert IsMinimalForm(s, result);
  } else {
    var k := count_zeros(s);
    assert 0 <= k;
    assert k <= |s|;
    var nk: nat := k as nat;
    result := "1" + seq(nk, _ => '0');
    ValidBinaryStringOfOneZeros(nk);
    assert IsMinimalForm(s, result);
  }
}
// </vc-code>

