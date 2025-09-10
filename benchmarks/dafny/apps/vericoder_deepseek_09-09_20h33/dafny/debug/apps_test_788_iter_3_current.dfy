predicate ValidInput(s: string) 
{
    |s| == 7 && s[0] == 'A' && forall i :: 1 <= i < 7 ==> '0' <= s[i] <= '9'
}

function DigitSum(s: string, start: int, end: int): int
    requires 0 <= start <= end <= |s|
    requires forall i :: start <= i < end ==> '0' <= s[i] <= '9'
    decreases end - start
{
    if start >= end then 0
    else (s[start] as int - '0' as int) + DigitSum(s, start + 1, end)
}

function ZeroCount(s: string, start: int, end: int): int
    requires 0 <= start <= end <= |s|
    decreases end - start
{
    if start >= end then 0
    else (if s[start] == '0' then 1 else 0) + ZeroCount(s, start + 1, end)
}

// <vc-helpers>
lemma ZeroCountLemma(s: string, start: int, end: int)
    requires 0 <= start <= end <= |s|
    ensures start <= end ==> ZeroCount(s, start, end) == ZeroCount(s, start, start) + ZeroCount(s, start, end)
    decreases end - start
{
    if start >= end {
        return;
    }
    // Base case: when start >= end, both sides are 0
}

lemma ZeroCountLemmaHelper(s: string, start: int, end: int, count: int)
    requires 0 <= start <= end <= |s|
    requires 0 <= count
    ensures ZeroCount(s, start, end) == count + ZeroCount(s, start + count, end)
    decreases end - start - count
{
    if start + count >= end {
        assert ZeroCount(s, start + count, end) == 0;
        // The remaining part is handled by the base case of ZeroCount
    } else {
        if s[start + count] == '0' {
            ZeroCountLemmaHelper(s, start, end, count + 1);
        } else {
            ZeroCountLemmaHelper(s, start, end, count + 1);
        }
    }
}

lemma DigitSumLemma(s: string, start: int, end: int)
    requires 0 <= start <= end <= |s|
    requires forall i :: start <= i < end ==> '0' <= s[i] <= '9'
    ensures start < end ==> DigitSum(s, start, end) == (s[start] as int - '0' as int) + DigitSum(s, start + 1, end)
    decreases end - start
{
    if start < end {
        // The recursive case of DigitSum already gives this equality
    }
}
// </vc-helpers>

// <vc-spec>
method solve(s: string) returns (result: int)
    requires ValidInput(s)
    ensures result == DigitSum(s, 1, 7) + 9 * ZeroCount(s, 1, 7) + 1
// </vc-spec>
// <vc-code>
{
    var sum := 0;
    var zeros := 0;
    var i := 1;
    while i < 7
        invariant 1 <= i <= 7
        invariant sum == DigitSum(s, 1, i)
        invariant zeros == ZeroCount(s, 1, i)
    {
        if s[i] == '0' {
            zeros := zeros + 1;
        } else {
            sum := sum + (s[i] as int - '0' as int);
        }
        i := i + 1;
        if i <= 7 {
            DigitSumLemma(s, 1, i);
            ZeroCountLemma(s, 1, i);
        }
    }
    result := sum + 9 * zeros + 1;
}
// </vc-code>

