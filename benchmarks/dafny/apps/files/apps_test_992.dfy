Given N positive integers A₁, A₂, ..., Aₙ and a positive integer S,
for each non-empty subset T of {1, 2, ..., N}, define f(T) as the number 
of non-empty subsets of T whose corresponding A values sum to S.
Find the sum of f(T) over all 2ᴺ - 1 non-empty subsets T, modulo 998244353.

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

// No additional helper methods needed

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
{
    var lines := SplitLines(stdin_input);
    if |lines| < 2 {
        result := "0\n";
        return;
    }

    var first_line := SplitWhitespace(lines[0]);
    var second_line := SplitWhitespace(lines[1]);

    if |first_line| < 2 || |second_line| == 0 {
        result := "0\n";
        return;
    }

    var n := StringToInt(first_line[0]);
    var s := StringToInt(first_line[1]);

    if n <= 0 || s <= 0 || |second_line| != n {
        result := "0\n";
        return;
    }

    var a := seq(n, i requires 0 <= i < n => StringToInt(second_line[i]));

    if !ValidInput(n, s, a) {
        result := "0\n";
        return;
    }

    var mod := 998244353;
    var dp := seq(n+1, i => seq(s+1, j => 0));
    dp := dp[0 := dp[0][0 := 1]];

    var i := 1;
    while i <= n
        invariant 1 <= i <= n + 1
        invariant |dp| == n + 1
        invariant forall k :: 0 <= k < |dp| ==> |dp[k]| == s + 1
    {
        var new_row := seq(s+1, k => (dp[i-1][k] * 2) % mod);

        if 0 <= i-1 < n && 0 < a[i-1] <= s {
            var j := a[i-1];
            while j <= s
                invariant a[i-1] <= j <= s + 1
                invariant |new_row| == s + 1
            {
                if j - a[i-1] >= 0 && j - a[i-1] < s+1 {
                    new_row := new_row[j := (new_row[j] + dp[i-1][j - a[i-1]]) % mod];
                }
                j := j + 1;
            }
        }

        dp := dp[i := new_row];
        i := i + 1;
    }

    if s < |dp[n]| {
        result := IntToString(dp[n][s]) + "\n";
    } else {
        result := "0\n";
    }
}
