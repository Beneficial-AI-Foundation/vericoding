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
lemma DigitSumAdditive(s: string, start: int, mid: int, end: int)
    requires 0 <= start <= mid <= end <= |s|
    requires forall i :: start <= i < end ==> '0' <= s[i] <= '9'
    ensures DigitSum(s, start, end) == DigitSum(s, start, mid) + DigitSum(s, mid, end)
    decreases end - start
{
    if start >= end {
    } else if start >= mid {
    } else {
        DigitSumAdditive(s, start + 1, mid, end);
    }
}

lemma ZeroCountAdditive(s: string, start: int, mid: int, end: int)
    requires 0 <= start <= mid <= end <= |s|
    ensures ZeroCount(s, start, end) == ZeroCount(s, start, mid) + ZeroCount(s, mid, end)
    decreases end - start
{
    if start >= end {
    } else if start >= mid {
    } else {
        ZeroCountAdditive(s, start + 1, mid, end);
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
        invariant forall j :: 1 <= j < i ==> '0' <= s[j] <= '9'
    {
        assert '0' <= s[i] <= '9';
        
        DigitSumAdditive(s, 1, i, i + 1);
        assert DigitSum(s, 1, i + 1) == DigitSum(s, 1, i) + DigitSum(s, i, i + 1);
        assert DigitSum(s, i, i + 1) == s[i] as int - '0' as int;
        
        ZeroCountAdditive(s, 1, i, i + 1);
        assert ZeroCount(s, 1, i + 1) == ZeroCount(s, 1, i) + ZeroCount(s, i, i + 1);
        assert ZeroCount(s, i, i + 1) == (if s[i] == '0' then 1 else 0);
        
        digitSum := digitSum + (s[i] as int - '0' as int);
        if s[i] == '0' {
            zeroCount := zeroCount + 1;
        }
        
        i := i + 1;
    }
    
    result := digitSum + 9 * zeroCount + 1;
}
// </vc-code>

