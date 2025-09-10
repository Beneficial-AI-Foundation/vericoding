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
method SplitString(s: string) returns (parts: seq<string>)
    ensures parts == SplitStringPure(s)
{
    parts := [];
    var current := "";
    var i := 0;
    
    while i < |s|
        invariant 0 <= i <= |s|
        invariant parts + (if |current| > 0 then [current] else []) == 
            SplitStringHelper(s, i, current, parts)
    {
        if s[i] == ' ' || s[i] == '\n' {
            if |current| > 0 {
                parts := parts + [current];
                current := "";
            }
        } else {
            current := current + [s[i]];
        }
        i := i + 1;
    }
    
    if |current| > 0 {
        parts := parts + [current];
    }
}

method StringToInt(s: string) returns (n: int)
    ensures n == StringToIntPure(s)
{
    if |s| == 0 {
        n := 0;
        return;
    }
    
    var sign := 1;
    var start := 0;
    
    if s[0] == '-' {
        sign := -1;
        start := 1;
    }
    
    n := 0;
    var i := |s| - 1;
    var multiplier := 1;
    
    while i >= start
        invariant start - 1 <= i < |s|
        invariant multiplier > 0
        decreases i - start + 1
    {
        if '0' <= s[i] && s[i] <= '9' {
            n := n + (s[i] as int - '0' as int) * multiplier;
            multiplier := multiplier * 10;
        }
        i := i - 1;
    }
    
    n := n * sign;
}

method IntToString(n: int) returns (s: string)
    requires n >= -2000000000 && n <= 2000000000
    ensures s == IntToStringPure(n)
    ensures |s| > 0
{
    if n == 0 {
        s := "0";
        return;
    }
    
    var sign := "";
    var num := n;
    if n < 0 {
        sign := "-";
        num := -n;
    }
    
    s := "";
    var original := num;
    while num > 0
        invariant 0 <= num <= original
        invariant num == 0 ==> s == IntToStringPureHelper(original)
        decreases num
    {
        var digit := (num % 10) as char + '0' as char;
        s := [digit] + s;
        num := num / 10;
    }
    
    s := sign + s;
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
    var parts := SplitString(input);
    
    if |parts| >= 4 {
        var A := StringToInt(parts[0]);
        var B := StringToInt(parts[1]);
        var C := StringToInt(parts[2]);
        var K := StringToInt(parts[3]);
        
        if ValidInput(A, B, C, K) {
            var maxSum := MaxSum(A, B, C, K);
            
            if maxSum >= -2000000000 && maxSum <= 2000000000 {
                var resultStr := IntToString(maxSum);
                result := resultStr + "\n";
                return;
            }
        }
    }
    
    result := "0\n";
}
// </vc-code>

