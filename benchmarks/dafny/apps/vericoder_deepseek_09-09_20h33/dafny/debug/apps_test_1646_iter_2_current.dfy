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
lemma CountZerosLemma(s: string)
    requires ValidBinaryString(s)
    ensures count_zeros(s) == |s| - (if s == "0" then 0 else 1)
{
    if s == "0" {
        assert count_zeros("0") == 1;
        assert |s| == 1;
    } else {
        assert s[0] == '1';
        calc {
            count_zeros(s);
            == { assert s == s[0] + s[1..]; }
            (if s[0] == '0' then 1 else 0) + count_zeros(s[1..]);
            == { assert s[0] == '1'; }
            0 + count_zeros(s[1..]);
            ==
            count_zeros(s[1..]);
        }
        var sub := s[1..];
        if |sub| > 0 {
            CountZerosLemma(sub);
        }
        assert count_zeros(s) == count_zeros(sub);
        assert |s| == |sub| + 1;
    }
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
    CountZerosLemma(s);
    if s == "0" {
        result := "0";
    } else {
        var zeros := count_zeros(s);
        result := "1" + (seq(zeros, _ => '0'));
        assert result == "1" + (seq(zeros, _ => '0'));
    }
}
// </vc-code>

