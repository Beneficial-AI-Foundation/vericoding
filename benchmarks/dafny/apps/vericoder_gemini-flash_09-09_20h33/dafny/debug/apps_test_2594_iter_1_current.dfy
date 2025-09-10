predicate ValidInput(input: string)
{
    var lines := SplitLines(input);
    |lines| > 0 &&
    var t := ParseInt(lines[0]);
    t > 0 && |lines| >= t + 1 &&
    forall i {:trigger SplitSpaces(lines[i+1])} :: 0 <= i < t ==>
        var parts := SplitSpaces(lines[i+1]);
        |parts| >= 2 &&
        var n := ParseInt(parts[0]);
        var m := ParseInt(parts[1]);
        n >= 1 && m >= 1
}

function MinLanterns(n: int, m: int): int
    requires n >= 1 && m >= 1
{
    (n * m + 1) / 2
}

predicate ValidOutput(input: string, output: seq<int>)
    requires ValidInput(input)
{
    var lines := SplitLines(input);
    var t := ParseInt(lines[0]);
    |output| == t &&
    forall i {:trigger output[i]} :: 0 <= i < t ==>
        var parts := SplitSpaces(lines[i+1]);
        |parts| >= 2 &&
        var n := ParseInt(parts[0]);
        var m := ParseInt(parts[1]);
        n >= 1 && m >= 1 &&
        output[i] == MinLanterns(n, m)
}

// <vc-helpers>
function SplitLines(input: string): seq<string> {
    if input == "" then
        []
    else
        input.Split('\n')
}

function SplitSpaces(input: string): seq<string> {
    if input == "" then
        []
    else
        input.Split(' ')
}

function ParseInt(s: string): int
    requires forall c :: c in s ==> '0' <= c <= '9'
    ensures ParseInt(s) >= 0
{
    if s == "" then
        0
    else
        (s[0] as int - '0' as int) * (if |s| > 1 then 10 * ParseInt(s[1..]) else 1)
}
// </vc-helpers>

// <vc-spec>

// </vc-spec>
// <vc-code>
{
    var lines := SplitLines(input);
    var t := ParseInt(lines[0]);
    var output: seq<int> := [];
    for i := 0 to t - 1
        invariant 0 <= i <= t
        invariant |lines| > 0
        invariant var current_t := ParseInt(lines[0]); current_t == t
        invariant forall k :: 0 <= k < i ==>
            var parts := SplitSpaces(lines[k+1]);
            _ = parts; // To trigger the definition of parts
            |parts| >= 2 &&
            var n_k := ParseInt(parts[0]);
            var m_k := ParseInt(parts[1]);
            n_k >= 1 && m_k >= 1
            && output[k] == MinLanterns(n_k, m_k)
        invariant |output| == i
    {
        var line := lines[i+1];
        var parts := SplitSpaces(line);
        var n := ParseInt(parts[0]);
        var m := ParseInt(parts[1]);
        output := output + [MinLanterns(n, m)];
    }
    return output;
}
// </vc-code>

