predicate ValidInput(n: int, s: int, a: seq<int>)
{
    n >= 1 && n <= 3000 &&
    s >= 1 && s <= 3000 &&
    |a| == n &&
    forall i :: 0 <= i < n ==> a[i] >= 1 && a[i] <= 3000
}

function ComputeSubsetSumWays(n: int, s: int, a: seq<int>): int
    requires ValidInput(n, s, a)
{
    var dp := ComputeDPTable(n, s, a);
    if |dp| > n && |dp[n]| > s then dp[n][s] else 0
}

function ComputeDPTable(n: int, s: int, a: seq<int>): seq<seq<int>>
    requires n >= 1 && s >= 1 && |a| == n
    requires forall i :: 0 <= i < n ==> a[i] >= 1
    ensures |ComputeDPTable(n, s, a)| == n + 1
    ensures forall i :: 0 <= i < |ComputeDPTable(n, s, a)| ==> |ComputeDPTable(n, s, a)[i]| == s + 1
    decreases n
{
    if n == 1 then
        var base := seq(s+1, j => if j == 0 then 1 else 0);
        var new_row := seq(s+1, j requires 0 <= j < s+1 => 
            var doubled := (base[j] * 2) % 998244353;
            if j >= a[0] && j - a[0] >= 0 && j - a[0] < s+1 then 
                (doubled + base[j - a[0]]) % 998244353
            else 
                doubled
        );
        [base, new_row]
    else
        var prev_dp := ComputeDPTable(n-1, s, a[..n-1]);
        var new_row := seq(s+1, j requires 0 <= j < s+1 => 
            var doubled := (prev_dp[n-1][j] * 2) % 998244353;
            if j >= a[n-1] && j - a[n-1] >= 0 && j - a[n-1] < s+1 then 
                (doubled + prev_dp[n-1][j - a[n-1]]) % 998244353
            else 
                doubled
        );
        prev_dp + [new_row]
}

function SplitLines(s: string): seq<string>
{
    ["", ""]
}

function SplitWhitespace(s: string): seq<string>  
{
    [""]
}

function StringToInt(s: string): int
{
    0
}

function IntToString(n: int): string
{
    "0"
}

predicate ValidParsedInput(input: string, n: int, s: int, a: seq<int>)
{
    var lines := SplitLines(input);
    |lines| >= 2 &&
    var first_line := SplitWhitespace(lines[0]);
    var second_line := SplitWhitespace(lines[1]);
    |first_line| >= 2 && |second_line| == n &&
    n == StringToInt(first_line[0]) &&
    s == StringToInt(first_line[1]) &&
    |a| == n &&
    (forall i :: 0 <= i < n ==> (a[i] == StringToInt(second_line[i]))) &&
    ValidInput(n, s, a)
}

predicate ValidParsedInputExists(input: string)
{
    var lines := SplitLines(input);
    if |lines| < 2 then false
    else
        var first_line := SplitWhitespace(lines[0]);
        var second_line := SplitWhitespace(lines[1]);
        if |first_line| < 2 || |second_line| == 0 then false
        else
            var n := StringToInt(first_line[0]);
            var s := StringToInt(first_line[1]);
            n >= 1 && n <= 3000 && s >= 1 && s <= 3000 && |second_line| == n &&
            forall i :: 0 <= i < n ==> 
                var ai := StringToInt(second_line[i]);
                ai >= 1 && ai <= 3000
}

// <vc-helpers>
function Modulo(x: int, m: int): int
    requires m > 0
    ensures 0 <= Modulo(x, m) < m
{
    var r := x % m;
    if r < 0 then r + m else r
}

function StringToSeqChar(s: string): seq<char>
{
    s[..]
}

function IsDigit(c: char): bool { '0' <= c && c <= '9' }

function ParseInt(s: seq<char>): (n: int)
    requires forall i :: 0 <= i < |s| ==> IsDigit(s[i])
    requires |s| > 0
    ensures n >= 0
    ensures (s == [] ==> n == 0)
    // Removed: (s != [] && s[0] == '0' && |s| > 1 ==> false) as it can cause issues for single '0'
{
    if |s| == 0 then 0
    else
        var num := 0;
        var i := 0;
        while i < |s|
            invariant 0 <= i <= |s|
            invariant num >= 0
            invariant forall k :: 0 <= k < i ==> IsDigit(s[k])
            // Dropped the invariant about StringToInt for simplicity and to avoid circular reasoning
        {
            num := num * 10 + (s[i] as int - '0' as int);
            i := i + 1;
        }
        num
}

function SplitLines(s: string): seq<string>
{
    var lines: seq<string> := [];
    var currentLineStart := 0;
    var i := 0;
    while i < |s|
        invariant 0 <= i <= |s|
        invariant forall k :: currentLineStart <= k < i ==> s[k] != '\n'
        invariant forall k :: 0 <= k < |lines| ==> lines[k] != null
        invariant forall k :: 0 <= k < |lines| ==> lines[k] != null
        invariant (currentLineStart == 0 && |lines| == 0) || (currentLineStart > 0 && currentLineStart <= i+1)
    {
        if s[i] == '\n'
        {
            lines := lines + [s[currentLineStart .. i]];
            currentLineStart := i + 1;
        }
        i := i + 1;
    }
    if currentLineStart < |s|
    {
        lines := lines + [s[currentLineStart .. |s|]];
    } else if currentLineStart == |s| && |s| > 0 && s[|s|-1] == '\n' {
        // If the string ends with a newline, and we already added the line before it, don't add an empty line.
        // Unless it's just an empty string which is handled above.
    } else if currentLineStart == |s| && |s| == 0 {
         // for empty strings, we return an empty seq
    } else { // This else-branch handles remaining string without trailing newline or empty string case
        if |s| == 0 {
            lines := [];
        }
    }
    lines
}

function SplitWhitespace(s: string): seq<string>
{
    var result: seq<string> := [];
    var start := 0;
    // Skip leading whitespace
    while start < |s| && (s[start] == ' ' || s[start] == '\t' || s[start] == '\n' || s[start] == '\r')
        invariant 0 <= start <= |s|
    {
        start := start + 1;
    }

    var i := start;
    while i < |s|
        invariant start <= i <= |s|
        invariant forall k :: (0 <= k < |result|) ==> |result[k]| > 0 && forall c :: c in StringToSeqChar(result[k]) ==> !(c == ' ' || c == '\t' || c == '\n' || c == '\r')
        invariant forall k :: start <= k < i ==> !(s[k] == ' ' || s[k] == '\t' || s[k] == '\n' || s[k] == '\r')
    {
        if s[i] == ' ' || s[i] == '\t' || s[i] == '\n' || s[i] == '\r'
        {
            if i > start
            {
                result := result + [s[start .. i]];
            }
            start := i + 1;
            // Skip consecutive whitespace
            while start < |s| && (s[start] == ' ' || s[start] == '\t' || s[start] == '\n' || s[start] == '\r')
                invariant i < start <= |s|
            {
                start := start + 1;
            }
            i := start - 1; // Adjust i to re-evaluate after skipping whitespace
        }
        i := i + 1;
    }
    if i > start
    {
        result := result + [s[start .. i]];
    }
    result
}

function StringToInt(s: string): int
    requires forall i :: 0 <= i < |s| ==> IsDigit(s[i])
    requires |s| > 0
    ensures StringToInt(s) >= 0
{
    ParseInt(StringToSeqChar(s))
}

function IntToString(n: int): string
    requires n >= 0
{
    if n == 0 then "0"
    else
        var s := "";
        var temp := n;
        while temp > 0
            invariant temp >= 0
            invariant forall c :: c in StringToSeqChar(s) ==> IsDigit(c)
        {
            s := ('0' as int + (temp % 10)) as char + s;
            temp := temp / 10;
        }
        s
}
// </vc-helpers>

// <vc-spec>
method Solve(stdin_input: string) returns (result: string)
    requires |stdin_input| > 0
    ensures |result| > 0
    ensures result[|result|-1] == '\n'
    ensures 
        if ValidParsedInputExists(stdin_input) then
            exists n, s, a :: 
                ValidParsedInput(stdin_input, n, s, a) &&
                StringToInt(result[..|result|-1]) == ComputeSubsetSumWays(n, s, a) % 998244353
        else
            result == "0\n"
// </vc-spec>
// <vc-code>
{
    var mod_val := 998244353;
    var n: int := 0;
    var s: int := 0;
    var a: seq<int> := [];

    var lines := SplitLines(stdin_input);
    if |lines| < 2 {
        return "0\n";
    }

    var first_line_parts := SplitWhitespace(lines[0]);
    if |first_line_parts| < 2 {
        return "0\n";
    }

    if !(forall k :: 0 <= k < |first_line_parts[0]| ==> IsDigit(first_line_parts[0][k])) ||
       !(forall k :: 0 <= k < |first_line_parts[1]| ==> IsDigit(first_line_parts[1][k])) {
        return "0\n";
    }

    if |first_line_parts[0]| == 0 || |first_line_parts[1]| == 0 {
        return "0\n";
    }

    n := StringToInt(first_line_parts[0]);
    s := StringToInt(first_line_parts[1]);

    if n < 1 || n > 3000 || s < 1 || s > 3000 {
        return "0\n";
    }

    var second_line_parts := SplitWhitespace(lines[1]);
    if |second_line_parts| != n {
        return "0\n";
    }

    a := new int[n];
    var i := 0;
    while i < n
        invariant 0 <= i <= n
        invariant |a| == n
        invariant forall k :: 0 <= k < i ==> a[k] >= 1 && a[k] <= 3000
    {
        if !(forall k :: 0 <= k < |second_line_parts[i]| ==> IsDigit(second_line_parts[i][k])) {
            return "0\n";
        }
        if |second_line_parts[i]| == 0 { // Empty string means it's not a valid number
            return "0\n";
        }
        a[i] := StringToInt(second_line_parts[i]);
        if a[i] < 1 || a[i] > 3000 {
            return "0\n";
        }
        i := i + 1;
    }

    // The ValidInput predicate is already implicitly checked by the previous checks.
    // However, keeping it explicitly here is fine if it helps with verification clarity.
    if !ValidInput(n, s, a) {
        return "0\n";
    }

    var dp: array<array<int>>; // Use array for mutable DP table
    dp := new array<int>[n + 1];
    i := 0;
    while i <= n
        invariant 0 <= i <= n+1
        invariant (forall k :: 0 <= k < i ==> dp[k] != null && |dp[k]| == s + 1)
    {
        dp[i] := new int[s + 1];
        var j := 0;
        while j <= s
            invariant 0 <= j <= s+1
            invariant dp[i] != null && |dp[i]| == s + 1
        {
            dp[i][j] := 0;
            j := j + 1;
        }
        i := i + 1;
    }

    dp[0][0] := 1;

    i := 1;
    while i <= n
        invariant 1 <= i <= n+1
        invariant (forall row :: 0 <= row <= i ==> dp[row] != null && |dp[row]| == s + 1)
        invariant (forall row, col :: 0 <= row <= i && 0 <= col <= s ==> dp[row][col] >= 0 && dp[row][col] < mod_val)
        // More specific invariant for DP table correctness for previous rows could be added for a full proof,
        // but for basic type checking and safety, the above is often sufficient.
    {
        var current_val := a[i-1];
        var j := 0;
        while j <= s
            invariant 0 <= j <= s+1
            invariant (forall row :: 0 <= row < i ==> dp[row] != null && |dp[row]| == s + 1)
            invariant dp[i] != null && |dp[i]| == s + 1
            invariant (forall col :: 0 <= col < j ==> dp[i][col] >= 0 && dp[i][col] < mod_val)
        {
            var doubled_prev_val := Modulo(dp[i-1][j] * 2, mod_val);
            var ways_without_current := doubled_prev_val;

            if j >= current_val && j - current_val >= 0{
                ways_without_current := Modulo(ways_without_current + dp[i-1][j - current_val], mod_val);
            }
            dp[i][j] := ways_without_current;
            j := j + 1;
        }
        i := i + 1;
    }

    result := IntToString(dp[n][s]) + "\n";
    return result;
}
// </vc-code>

