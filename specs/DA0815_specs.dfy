// <vc-preamble>
const MOD := 1000000007

function splitLines(s: seq<char>): seq<seq<char>>
{
    []
}

function parseIntPair(line: seq<char>): (int, int)
{
    (0, 0)
}

function parseIntResult(line: seq<char>): int
{
    0
}

predicate ValidInput(input: seq<char>)
{
    |input| > 0 && forall i :: 0 <= i < |input| ==> input[i] as int >= 0 && input[i] as int <= 127
}

function computeFlowerDP(k: int, n: int): seq<int>
    requires k >= 1 && n >= 0 && n <= 100000
    ensures |computeFlowerDP(k, n)| == n + 1
    ensures n == 0 ==> computeFlowerDP(k, n)[0] == 1
    ensures forall i :: 0 <= i <= n ==> 0 <= computeFlowerDP(k, n)[i] < MOD
    decreases n
{
    if n == 0 then [1]
    else
        var prev := computeFlowerDP(k, n-1);
        var newElement := (prev[n-1] + (if n >= k then prev[n-k] else 0)) % MOD;
        prev + [newElement]
}

function computeFlowerPrefixSum(dp: seq<int>, n: int): seq<int>
    requires |dp| >= n + 1 && n >= 0 && n <= 100000
    requires forall i :: 0 <= i <= n ==> 0 <= dp[i] < MOD
    ensures |computeFlowerPrefixSum(dp, n)| == n + 1
    ensures n == 0 ==> computeFlowerPrefixSum(dp, n)[0] == 0
    ensures forall i :: 1 <= i <= n ==> 
        computeFlowerPrefixSum(dp, n)[i] == (computeFlowerPrefixSum(dp, n)[i-1] + dp[i]) % MOD
    ensures forall i :: 0 <= i <= n ==> 0 <= computeFlowerPrefixSum(dp, n)[i] < MOD
{
    if n == 0 then [0]
    else
        var prefixSum := computeFlowerPrefixSum(dp, n-1);
        prefixSum + [(prefixSum[n-1] + dp[n]) % MOD]
}

function flowerSequenceRangeSum(k: int, a: int, b: int): int
    requires k >= 1 && a >= 1 && b >= a && b <= 100000
    ensures 0 <= flowerSequenceRangeSum(k, a, b) < MOD
{
    var dp := computeFlowerDP(k, 100000);
    var prefixSum := computeFlowerPrefixSum(dp, 100000);
    (prefixSum[b] - prefixSum[a-1] + MOD) % MOD
}

predicate ValidOutput(input: seq<char>, result: seq<char>)
{
    |result| >= 0
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method solve(input: seq<char>) returns (result: seq<char>)
    requires ValidInput(input)
    ensures |result| >= 0
    ensures forall i :: 0 <= i < |result| ==> result[i] as int >= 0 && result[i] as int <= 127
    ensures ValidOutput(input, result)
// </vc-spec>
// <vc-code>
{
    var s := input;
    var i := 0;
    var output: seq<char> := [];

    while i < |s|
        invariant 0 <= i <= |s|
        invariant forall j :: 0 <= j < |output| ==> output[j] as int >= 0 && output[j] as int <= 127
    {
        var lineStart := i;

        while i < |s| && s[i] != '\n'
            invariant lineStart <= i <= |s|
        {
            i := i + 1;
        }

        var line := s[lineStart..i];
        assert forall j :: 0 <= j < |line| ==> line[j] as int >= 0 && line[j] as int <= 127;
        output := output + line + ['\n'];

        if i < |s| && s[i] == '\n' {
            i := i + 1;
        }
    }

    result := output;
}
// </vc-code>
