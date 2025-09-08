Given a binary string with no redundant leading zeros, find the minimum possible binary string 
achievable using these operations: 1) Swap any two adjacent characters, 2) Replace "11" with "1".
The goal is to minimize the decimal value represented by the resulting binary string.

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

lemma count_zeros_slice_lemma(s: string, i: int)
    requires 0 <= i < |s|
    ensures count_zeros(s[0..i+1]) == count_zeros(s[0..i]) + (if s[i] == '0' then 1 else 0)
{
    if i == 0 {
        assert s[0..1] == [s[0]];
        assert s[0..0] == [];
        assert count_zeros([]) == 0;
    } else {
        assert s[0..i+1] == s[0..1] + s[1..i+1];
        assert s[0..i] == s[0..1] + s[1..i];
        assert count_zeros(s[0..i+1]) == (if s[0] == '0' then 1 else 0) + count_zeros(s[1..i+1]);
        assert count_zeros(s[0..i]) == (if s[0] == '0' then 1 else 0) + count_zeros(s[1..i]);
        assert (s[1..])[0..i] == s[1..i+1];
        assert (s[1..])[0..i-1] == s[1..i];
        assert (s[1..])[i-1] == s[i];
        count_zeros_slice_lemma(s[1..], i-1);
        assert count_zeros(s[1..i+1]) == count_zeros(s[1..i]) + (if s[i] == '0' then 1 else 0);
    }
}

lemma count_zeros_full_slice_lemma(s: string)
    ensures count_zeros(s[0..|s|]) == count_zeros(s)
{
    assert s[0..|s|] == s;
}

method solve(n: int, s: string) returns (result: string)
    requires n >= 1 && n <= 100
    requires |s| == n
    requires ValidBinaryString(s)
    ensures ValidBinaryString(result)
    ensures IsMinimalForm(s, result)
{
    if s == "0" {
        result := "0";
    } else {
        var zeroCount := 0;
        var i := 0;
        while i < |s|
            invariant 0 <= i <= |s|
            invariant zeroCount == count_zeros(s[0..i])
        {
            count_zeros_slice_lemma(s, i);
            if s[i] == '0' {
                zeroCount := zeroCount + 1;
            }
            i := i + 1;
        }
        count_zeros_full_slice_lemma(s);
        assert zeroCount == count_zeros(s);
        var tmpCall1 := seq(zeroCount, _ => '0');
        result := "1" + tmpCall1;
    }
}
