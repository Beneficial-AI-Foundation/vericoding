// <vc-preamble>
predicate ValidInput(values: seq<int>, s: string)
{
    |values| == 26 &&
    |s| > 0 &&
    (forall i :: 0 <= i < |s| ==> 'a' <= s[i] <= 'z') &&
    (forall i :: 0 <= i < |values| ==> -100000 <= values[i] <= 100000)
}

function CountValidSubstrings(values: seq<int>, s: string): int
    requires ValidInput(values, s)
    ensures CountValidSubstrings(values, s) >= 0
{
    CountValidSubstringsUpTo(values, s, |s|)
}

function CountValidSubstringsUpTo(values: seq<int>, s: string, pos: int): int
    requires ValidInput(values, s)
    requires 0 <= pos <= |s|
    ensures CountValidSubstringsUpTo(values, s, pos) >= 0
    decreases pos
{
    if pos == 0 then 0
    else CountValidSubstringsUpTo(values, s, pos - 1) + CountSubstringsStartingAt(values, s, pos - 1)
}

function CountSubstringsStartingAt(values: seq<int>, s: string, start: int): int
    requires ValidInput(values, s)
    requires 0 <= start < |s|
    ensures CountSubstringsStartingAt(values, s, start) >= 0
{
    CountSubstringsStartingAtUpTo(values, s, start, |s| + 1)
}

function CountSubstringsStartingAtUpTo(values: seq<int>, s: string, start: int, end: int): int
    requires ValidInput(values, s)
    requires 0 <= start < |s|
    requires start + 2 <= end <= |s| + 1
    ensures CountSubstringsStartingAtUpTo(values, s, start, end) >= 0
    decreases end - start - 2
{
    if end <= start + 2 then 0
    else 
        var count := if s[start] == s[end-2] && SumBetween(values, s, start+1, end-3) == 0 then 1 else 0;
        count + CountSubstringsStartingAtUpTo(values, s, start, end - 1)
}

function SumBetween(values: seq<int>, s: string, start: int, end: int): int
    requires ValidInput(values, s)
    requires 0 <= start <= end + 1 < |s| + 1
    decreases end - start + 1
{
    if start > end then 0
    else values[s[start] as int - 'a' as int] + SumBetween(values, s, start+1, end)
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method solve(values: seq<int>, s: string) returns (result: int)
    requires ValidInput(values, s)
    ensures result >= 0
    ensures result == CountValidSubstrings(values, s)
// </vc-spec>
// <vc-code>
{
    result := 0;
    var i := 0;
    while i < |s|
        invariant 0 <= i <= |s|
        invariant result >= 0
        invariant result == CountValidSubstringsUpTo(values, s, i)
    {
        var j := i + 2;
        while j <= |s|
            invariant i + 2 <= j <= |s| + 1
            invariant result >= 0
            invariant result == CountValidSubstringsUpTo(values, s, i) + CountSubstringsStartingAtUpTo(values, s, i, j)
        {
            if s[i] == s[j-1] && SumBetween(values, s, i+1, j-2) == 0 {
                result := result + 1;
            }
            j := j + 1;
        }
        i := i + 1;
    }
}
// </vc-code>
