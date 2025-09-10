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
lemma MinLanternsLemma(n: int, m: int)
    requires n >= 1 && m >= 1
    ensures MinLanterns(n, m) == (n * m + 1) / 2
{
}

lemma ParseIntLemma(s: string)
    ensures var result := ParseInt(s); result >= 0
{
}

lemma SplitLinesLemma(input: string)
    ensures var lines := SplitLines(input); |lines| >= 0
{
}

lemma SplitSpacesLemma(line: string)
    ensures var parts := SplitSpaces(line); |parts| >= 0
{
}
// </vc-helpers>

// <vc-spec>

// </vc-spec>
// <vc-code>
{
    var lines := SplitLines(input);
    var t := ParseInt(lines[0]);
    var output := new int[t];
    var i := 0;
    while i < t
        invariant 0 <= i <= t
        invariant forall j :: 0 <= j < i ==> 
            var parts := SplitSpaces(lines[j+1]);
            var n := ParseInt(parts[0]);
            var m := ParseInt(parts[1]);
            output[j] == MinLanterns(n, m)
    {
        var parts := SplitSpaces(lines[i+1]);
        var n := ParseInt(parts[0]);
        var m := ParseInt(parts[1]);
        output[i] := (n * m + 1) / 2;
        i := i + 1;
    }
    output
}
// </vc-code>

