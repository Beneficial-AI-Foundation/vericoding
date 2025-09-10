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
lemma CountZerosCorrect(s: string)
    ensures count_zeros(s) == |set i | 0 <= i < |s| && s[i] == '0'|
{
    if |s| == 0 {
        assert count_zeros(s) == 0;
    } else {
        CountZerosCorrect(s[1..]);
    }
}

lemma ValidBinaryStringMinimalForm(s: string, result: string)
    requires ValidBinaryString(s)
    requires IsMinimalForm(s, result)
    ensures ValidBinaryString(result)
{
    if s == "0" {
        assert result == "0";
        assert ValidBinaryString(result);
    } else {
        assert result == "1" + seq(count_zeros(s), _ => '0');
        assert |result| > 0;
        assert result[0] == '1';
        if |result| > 1 {
            forall i | 1 <= i < |result|
                ensures result[i] == '0' || result[i] == '1'
            {
                assert result[i] == '0';
            }
        }
        assert ValidBinaryString(result);
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
    if s == "0" {
        result := "0";
    } else {
        var zeros := count_zeros(s);
        result := "1" + seq(zeros, _ => '0');
    }
    ValidBinaryStringMinimalForm(s, result);
}
// </vc-code>

