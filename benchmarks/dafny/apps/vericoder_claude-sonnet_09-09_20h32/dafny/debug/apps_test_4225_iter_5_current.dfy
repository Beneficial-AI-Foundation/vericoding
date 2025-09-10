predicate ValidInput(A: int, B: int, C: int, K: int)
{
    A >= 0 && B >= 0 && C >= 0 && K >= 1 && K <= A + B + C
}

function MaxSum(A: int, B: int, C: int, K: int): int
    requires ValidInput(A, B, C, K)
{
    if K <= A + B then
        if K <= A then K else A
    else
        A - (K - A - B)
}

predicate ParsedValues(input: string, A: int, B: int, C: int, K: int)
{
    exists parts :: |parts| >= 4 && 
        parts == SplitStringPure(input) &&
        A == StringToIntPure(parts[0]) &&
        B == StringToIntPure(parts[1]) &&
        C == StringToIntPure(parts[2]) &&
        K == StringToIntPure(parts[3]) &&
        ValidInput(A, B, C, K)
}

function IntToStringPure(n: int): string
    requires n >= -2000000000 && n <= 2000000000
    ensures |IntToStringPure(n)| > 0
{
    if n == 0 then "0"
    else if n < 0 then "-" + IntToStringPureHelper(-n)
    else IntToStringPureHelper(n)
}

function IntToStringPureHelper(n: int): string
    requires n > 0
    ensures |IntToStringPureHelper(n)| > 0
    decreases n
{
    if n < 10 then [('0' as int + n) as char]
    else IntToStringPureHelper(n / 10) + [('0' as int + (n % 10)) as char]
}

function SplitStringPure(s: string): seq<string>
{
    if |s| == 0 then []
    else SplitStringHelper(s, 0, "", [])
}

function SplitStringHelper(s: string, i: int, current: string, parts: seq<string>): seq<string>
    requires 0 <= i <= |s|
    decreases |s| - i
{
    if i >= |s| then
        if |current| > 0 then parts + [current] else parts
    else if s[i] == ' ' || s[i] == '\n' then
        if |current| > 0 then 
            SplitStringHelper(s, i+1, "", parts + [current])
        else 
            SplitStringHelper(s, i+1, "", parts)
    else
        SplitStringHelper(s, i+1, current + [s[i]], parts)
}

function StringToIntPure(s: string): int
{
    if |s| == 0 then 0
    else if s[0] == '-' then -StringToIntHelper(s, 1)
    else StringToIntHelper(s, 0)
}

function StringToIntHelper(s: string, start: int): int
    requires 0 <= start <= |s|
    decreases |s| - start
{
    if start >= |s| then 0
    else if '0' <= s[start] <= '9' then
        (s[start] as int - '0' as int) + 10 * StringToIntHelper(s, start + 1)
    else
        StringToIntHelper(s, start + 1)
}

// <vc-helpers>
lemma StringToIntHelperBounds(s: string, start: int)
    requires 0 <= start <= |s|
    ensures StringToIntHelper(s, start) >= 0
    ensures StringToIntHelper(s, start) <= 2000000000
    decreases |s| - start
{
    if start >= |s| {
        assert StringToIntHelper(s, start) == 0;
    } else if '0' <= s[start] <= '9' {
        StringToIntHelperBounds(s, start + 1);
        var digit := s[start] as int - '0' as int;
        var rest := StringToIntHelper(s, start + 1);
        assert digit >= 0 && digit <= 9;
        assert rest >= 0 && rest <= 2000000000;
        assert StringToIntHelper(s, start) == digit + 10 * rest;
        if rest <= 200000000 {
            assert 10 * rest <= 2000000000;
            assert digit + 10 * rest <= 9 + 2000000000;
        }
    } else {
        StringToIntHelperBounds(s, start + 1);
        assert StringToIntHelper(s, start) == StringToIntHelper(s, start + 1);
    }
}

lemma StringToIntBounds(s: string)
    ensures StringToIntPure(s) >= -2000000000 && StringToIntPure(s) <= 2000000000
{
    if |s| == 0 {
        assert StringToIntPure(s) == 0;
    } else if s[0] == '-' {
        StringToIntHelperBounds(s, 1);
        assert StringToIntHelper(s, 1) >= 0 && StringToIntHelper(s, 1) <= 2000000000;
        assert StringToIntPure(s) == -StringToIntHelper(s, 1);
        assert StringToIntPure(s) >= -2000000000 && StringToIntPure(s) <= 0;
    } else {
        StringToIntHelperBounds(s, 0);
        assert StringToIntHelper(s, 0) >= 0 && StringToIntHelper(s, 0) <= 2000000000;
        assert StringToIntPure(s) == StringToIntHelper(s, 0);
    }
}

lemma MaxSumBounds(A: int, B: int, C: int, K: int)
    requires ValidInput(A, B, C, K)
    ensures MaxSum(A, B, C, K) >= -2000000000 && MaxSum(A, B, C, K) <= 2000000000
{
    assert A >= 0 && B >= 0 && C >= 0 && K >= 1 && K <= A + B + C;
    
    if K <= A + B {
        if K <= A {
            assert MaxSum(A, B, C, K) == K;
            assert K >= 1 && K <= A;
            assert K <= 2000000000;
            assert K >= -2000000000;
        } else {
            assert MaxSum(A, B, C, K) == A;
            assert A >= 0;
            assert A <= 2000000000;
            assert A >= -2000000000;
        }
    } else {
        assert MaxSum(A, B, C, K) == A - (K - A - B);
        assert K > A + B;
        assert K <= A + B + C;
        var deficit := K - A - B;
        assert deficit > 0;
        assert deficit <= C;
        assert MaxSum(A, B, C, K) == A - deficit;
        assert A - deficit >= A - C;
        assert A >= 0 && C >= 0;
        assert A - deficit >= -C;
        assert A - deficit >= -2000000000;
        assert A - deficit <= A;
        assert A - deficit <= 2000000000;
    }
}

lemma ParsedValuesExistence(input: string, A: int, B: int, C: int, K: int)
    requires |input| > 0
    requires SplitStringPure(input) == SplitStringPure(input)
    requires |SplitStringPure(input)| >= 4
    requires A == StringToIntPure(SplitStringPure(input)[0])
    requires B == StringToIntPure(SplitStringPure(input)[1])
    requires C == StringToIntPure(SplitStringPure(input)[2])
    requires K == StringToIntPure(SplitStringPure(input)[3])
    requires ValidInput(A, B, C, K)
    ensures ParsedValues(input, A, B, C, K)
{
    var parts := SplitStringPure(input);
    assert |parts| >= 4;
    assert parts == SplitStringPure(input);
    assert A == StringToIntPure(parts[0]);
    assert B == StringToIntPure(parts[1]);
    assert C == StringToIntPure(parts[2]);
    assert K == StringToIntPure(parts[3]);
    assert ValidInput(A, B, C, K);
}
// </vc-helpers>

// <vc-spec>
method solve(input: string) returns (result: string)
    requires |input| > 0
    ensures |result| > 0
    ensures result[|result|-1] == '\n'
    ensures (exists A, B, C, K :: 
        ParsedValues(input, A, B, C, K) &&
        (var maxSum := MaxSum(A, B, C, K);
         maxSum >= -2000000000 && maxSum <= 2000000000 &&
         result == IntToStringPure(maxSum) + "\n")) ||
    (forall A, B, C, K :: !ParsedValues(input, A, B, C, K) ==> result == "0\n")
// </vc-spec>
// <vc-code>
{
    var parts := SplitStringPure(input);
    
    if |parts| >= 4 {
        var A := StringToIntPure(parts[0]);
        var B := StringToIntPure(parts[1]);
        var C := StringToIntPure(parts[2]);
        var K := StringToIntPure(parts[3]);
        
        StringToIntBounds(parts[0]);
        StringToIntBounds(parts[1]);
        StringToIntBounds(parts[2]);
        StringToIntBounds(parts[3]);
        
        if ValidInput(A, B, C, K) {
            ParsedValuesExistence(input, A, B, C, K);
            var maxSum := MaxSum(A, B, C, K);
            MaxSumBounds(A, B, C, K);
            assert maxSum >= -2000000000 && maxSum <= 2000000000;
            result := IntToStringPure(maxSum) + "\n";
        } else {
            result := "0\n";
        }
    } else {
        result := "0\n";
    }
}
// </vc-code>

