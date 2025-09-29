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
lemma DigitSumUnfold(s: string, start: int, end: int)
    requires 0 <= start < end <= |s|
    requires forall i :: start <= i < end ==> '0' <= s[i] <= '9'
    ensures DigitSum(s, start, end) == (s[start] as int - '0' as int) + DigitSum(s, start + 1, end)
{
}

lemma ZeroCountUnfold(s: string, start: int, end: int)
    requires 0 <= start < end <= |s|
    ensures ZeroCount(s, start, end) == (if s[start] == '0' then 1 else 0) + ZeroCount(s, start + 1, end)
{
}

lemma DigitSumExtend(s: string, start: int, end: int)
    requires 0 <= start <= end < |s|
    requires forall i :: start <= i <= end ==> '0' <= s[i] <= '9'
    ensures DigitSum(s, start, end + 1) == DigitSum(s, start, end) + (s[end] as int - '0' as int)
    decreases end - start
{
    if start == end {
        assert DigitSum(s, start, end) == 0;
        assert DigitSum(s, start, end + 1) == s[end] as int - '0' as int;
    } else {
        DigitSumUnfold(s, start, end + 1);
        DigitSumExtend(s, start + 1, end);
    }
}

lemma ZeroCountExtend(s: string, start: int, end: int)
    requires 0 <= start <= end < |s|
    ensures ZeroCount(s, start, end + 1) == ZeroCount(s, start, end) + (if s[end] == '0' then 1 else 0)
    decreases end - start
{
    if start == end {
        assert ZeroCount(s, start, end) == 0;
        assert ZeroCount(s, start, end + 1) == (if s[end] == '0' then 1 else 0);
    } else {
        ZeroCountUnfold(s, start, end + 1);
        ZeroCountExtend(s, start + 1, end);
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
    var digitSum := 0;
    var zeroCount := 0;
    var i := 1;
    
    while i < 7
        invariant 1 <= i <= 7
        invariant digitSum == DigitSum(s, 1, i)
        invariant zeroCount == ZeroCount(s, 1, i)
    {
        DigitSumExtend(s, 1, i);
        ZeroCountExtend(s, 1, i);
        
        var digit := s[i] as int - '0' as int;
        digitSum := digitSum + digit;
        
        if s[i] == '0' {
            zeroCount := zeroCount + 1;
        }
        
        i := i + 1;
    }
    
    result := digitSum + 9 * zeroCount + 1;
}
// </vc-code>

