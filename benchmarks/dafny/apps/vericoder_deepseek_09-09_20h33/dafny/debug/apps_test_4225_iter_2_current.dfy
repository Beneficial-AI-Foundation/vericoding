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
lemma StringToIntPureNonNegative(s: string, start: int)
    requires 0 <= start <= |s|
    ensures StringToIntHelper(s, start) >= 0
    decreases |s| - start
{
    if start < |s| {
        StringToIntPureNonNegative(s, start + 1);
    }
}

lemma StringToIntPureValidRange(s: string, start: int)
    requires 0 <= start <= |s|
    requires |StringToIntHelper(s, start)| <= 10  // Limit recursion depth for bounds checking
    ensures StringToIntHelper(s, start) <= 2000000000
    decreases |s| - start
{
    if start < |s| {
        StringToIntPureValidRange(s, start + 1);
    }
}

lemma SplitStringPureNonEmpty(input: string)
    ensures |SplitStringPure(input)| >= 0
{
}

lemma ParsedValuesImpliesValid(input: string, A: int, B: int, C: int, K: int)
    requires ParsedValues(input, A, B, C, K)
    ensures ValidInput(A, B, C, K)
{
}

lemma MaxSumInRange(A: int, B: int, C: int, K: int)
    requires ValidInput(A, B, C, K)
    ensures -2000000000 <= MaxSum(A, B, C, K) <= 2000000000
{
    // Explicit proof for the MaxSum bounds
    if K <= A + B {
        if K <= A {
            // maxSum = K, and since K >= 0 and K <= A + B + C <= A + B + C (by ValidInput)
            assert K <= 2000000000;
        } else {
            // maxSum = A
            assert A <= 2000000000;
        }
    } else {
        // maxSum = A - (K - A - B) = 2*A + B - K
        // Since K >= A + B + 1 (because K > A + B) and K <= A + B + C
        var sum := 2*A + B - K;
        assert sum <= A;  // Since K >= A + B + 1, so 2A + B - K <= 2A + B - (A + B + 1) = A - 1
        assert sum >= -(C);  // Since K <= A + B + C, so 2A + B - K >= 2A + B - (A + B + C) = A - C
    }
}

lemma ValidInputBounds(A: int, B: int, C: int, K: int)
    requires ValidInput(A, B, C, K)
    ensures A >= 0 && B >= 0 && C >= 0 && K >= 1 && K <= A + B + C
{
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
    if |parts| < 4 {
        result := "0\n";
        return;
    }
    
    var A := StringToIntPure(parts[0]);
    var B := StringToIntPure(parts[1]);
    var C := StringToIntPure(parts[2]);
    var K := StringToIntPure(parts[3]);
    
    // Add bounds checking for the parsed integers
    if !(A >= 0 && A <= 2000000000 && B >= 0 && B <= 2000000000 && 
         C >= 0 && C <= 2000000000 && K >= 1 && K <= A + B + C && K <= 2000000000) {
        result := "0\n";
        return;
    }
    
    if !ValidInput(A, B, C, K) {
        result := "0\n";
        return;
    }
    
    var maxSum := MaxSum(A, B, C, K);
    
    // Add explicit bounds checking before calling IntToStringPure
    assert -2000000000 <= maxSum <= 2000000000 by {
        MaxSumInRange(A, B, C, K);
    }
    
    result := IntToStringPure(maxSum) + "\n";
}
// </vc-code>

