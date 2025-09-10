predicate ValidInput(n: int, colors: seq<char>)
{
    1 <= n <= 100 &&
    |colors| == n &&
    (forall c | c in colors :: c in {'P', 'W', 'G', 'Y'}) &&
    'P' in colors && 'W' in colors && 'G' in colors
}

function DistinctColors(colors: seq<char>): set<char>
{
    set c | c in colors
}

function SolutionString(distinctCount: int): string
    requires distinctCount == 3 || distinctCount == 4
{
    if distinctCount == 3 then "Three" else "Four"
}

// <vc-helpers>
lemma DistinctColorsSizeLemma(n: int, colors: seq<char>)
    requires ValidInput(n, colors)
    ensures |DistinctColors(colors)| == 3 || |DistinctColors(colors)| == 4
{
    // The lemma is automatically true because ValidInput ensures 'P', 'W', 'G' are present
    // and colors can only contain {'P', 'W', 'G', 'Y'}, so distinct colors must be 3 or 4
}
// </vc-helpers>

// <vc-spec>
method Solve(n: int, colors: seq<char>) returns (result: string)
    requires ValidInput(n, colors)
    ensures var distinctColors := DistinctColors(colors);
            |distinctColors| == 3 || |distinctColors| == 4
    ensures var distinctColors := DistinctColors(colors);
            (|distinctColors| == 3 ==> result == "Three") &&
            (|distinctColors| == 4 ==> result == "Four")
    ensures result == "Three" || result == "Four"
// </vc-spec>
// <vc-code>
{
    DistinctColorsSizeLemma(n, colors);
    var distinctColors := DistinctColors(colors);
    if |distinctColors| == 3 {
        result := "Three";
    } else {
        result := "Four";
    }
}
// </vc-code>

