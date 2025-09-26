// <vc-preamble>
predicate isValidChar(c: char)
{
    ('0' <= c <= '9') || c == '?'
}

predicate isValidString(s: string)
{
    |s| > 0 && forall i :: 0 <= i < |s| ==> isValidChar(s[i])
}

function digitValue(c: char): int
    requires '0' <= c <= '9'
{
    c as int - '0' as int
}

function stringToInt(s: string): int
    requires |s| > 0
    requires forall i :: 0 <= i < |s| ==> '0' <= s[i] <= '9'
    decreases |s|
{
    if |s| == 1 then digitValue(s[0])
    else stringToInt(s[..|s|-1]) * 10 + digitValue(s[|s|-1])
}

predicate isValidReplacement(original: string, replacement: string)
    requires isValidString(original)
{
    |replacement| == |original| &&
    forall i :: 0 <= i < |original| ==>
        if original[i] == '?' then '0' <= replacement[i] <= '9'
        else replacement[i] == original[i]
}

function allDigitStrings(length: nat): set<string>
    decreases length
{
    if length == 0 then {""}
    else 
        set s, c | s in allDigitStrings(length-1) && '0' <= c <= '9' :: s + [c]
}

function countValidReplacements(s: string): nat
    requires isValidString(s)
{
    |set replacement | 
        replacement in allDigitStrings(|s|) &&
        isValidReplacement(s, replacement) &&
        stringToInt(replacement) % 13 == 5|
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method solve(s: string) returns (result: int)
    requires isValidString(s)
    ensures 0 <= result < 1000000007
// </vc-spec>
// <vc-code>
{
    var MOD := 1000000007;
    var ans := new int[13];
    var i := 0;
    while i < 13
        invariant 0 <= i <= 13
        invariant forall k :: 0 <= k < i ==> ans[k] == 0
    {
        ans[i] := 0;
        i := i + 1;
    }
    ans[0] := 1;

    var pos := 0;
    while pos < |s|
        invariant 0 <= pos <= |s|
        invariant forall k :: 0 <= k < 13 ==> 0 <= ans[k] < MOD
    {
        var dp := new int[26];
        var j := 0;
        while j < 26
            invariant 0 <= j <= 26
            invariant forall k :: 0 <= k < j ==> dp[k] == 0
        {
            dp[j] := 0;
            j := j + 1;
        }

        // Fill dp based on current ans
        j := 0;
        while j < 13
            invariant 0 <= j <= 13
            invariant forall k :: 0 <= k < j ==> dp[(k * 10) % 13] == ans[k] % MOD
            invariant forall k :: 0 <= k < 26 ==> 0 <= dp[k] < MOD
        {
            dp[(j * 10) % 13] := ans[j] % MOD;
            j := j + 1;
        }

        // Double the array (dp += dp in Python)
        j := 0;
        while j < 13
            invariant 0 <= j <= 13
            invariant forall k :: 0 <= k < j ==> dp[k + 13] == dp[k]
            invariant forall k :: 0 <= k < 26 ==> 0 <= dp[k] < MOD
        {
            dp[j + 13] := dp[j];
            j := j + 1;
        }

        if s[pos] == '?' {
            // For '?', sum dp[j+4:j+14] for each j
            j := 0;
            while j < 13
                invariant 0 <= j <= 13
                invariant forall k :: 0 <= k < j ==> 0 <= ans[k] < MOD
                invariant forall k :: 0 <= k < 26 ==> 0 <= dp[k] < MOD
            {
                var sum := 0;
                var k := j + 4;
                while k < j + 14
                    invariant j + 4 <= k <= j + 14
                    invariant 0 <= sum < MOD
                    invariant forall m :: 0 <= m < 26 ==> 0 <= dp[m] < MOD
                {
                    sum := (sum + dp[k]) % MOD;
                    k := k + 1;
                }
                ans[j] := sum;
                j := j + 1;
            }
        } else {
            // For specific digit
            var digit := s[pos] as int - '0' as int;
            j := 0;
            while j < 13
                invariant 0 <= j <= 13
                invariant forall k :: 0 <= k < j ==> 0 <= ans[k] < MOD
                invariant forall k :: 0 <= k < 26 ==> 0 <= dp[k] < MOD
                invariant 0 <= digit <= 9
            {
                ans[j] := dp[j + 13 - digit];
                j := j + 1;
            }
        }

        pos := pos + 1;
    }

    result := ans[5] % MOD;
}
// </vc-code>
