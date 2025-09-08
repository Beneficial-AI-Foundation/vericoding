Given A cards with value 1, B cards with value 0, and C cards with value -1,
find the maximum possible sum when picking exactly K cards.
The optimal strategy is to pick cards with highest values first.

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

method SplitString(s: string) returns (parts: seq<string>)
    ensures |parts| >= 0
    ensures parts == SplitStringPure(s)
{
    parts := SplitStringPure(s);
}

method StringToInt(s: string) returns (result: int)
    ensures result >= -2000000000 && result <= 2000000000
{
    var pureResult := StringToIntPure(s);
    if pureResult < -2000000000 {
        result := -2000000000;
    } else if pureResult > 2000000000 {
        result := 2000000000;
    } else {
        result := pureResult;
    }
}

method IntToString(n: int) returns (result: string)
    requires n >= -2000000000 && n <= 2000000000
    ensures |result| > 0
    ensures result == IntToStringPure(n)
{
    result := IntToStringPure(n);
}

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
{
    var parts := SplitString(input);
    if |parts| < 4 {
        result := "0\n";
        return;
    }

    var A_raw := StringToIntPure(parts[0]);
    var B_raw := StringToIntPure(parts[1]); 
    var C_raw := StringToIntPure(parts[2]);
    var K_raw := StringToIntPure(parts[3]);

    if A_raw < 0 || B_raw < 0 || C_raw < 0 || K_raw < 1 || K_raw > A_raw + B_raw + C_raw ||
       A_raw < -2000000000 || A_raw > 2000000000 ||
       B_raw < -2000000000 || B_raw > 2000000000 ||
       C_raw < -2000000000 || C_raw > 2000000000 ||
       K_raw < -2000000000 || K_raw > 2000000000 {
        result := "0\n";
        return;
    }

    var A := A_raw;
    var B := B_raw;
    var C := C_raw;
    var K := K_raw;

    var answer := MaxSum(A, B, C, K);
    var answerStr := IntToString(answer);
    result := answerStr + "\n";
}
