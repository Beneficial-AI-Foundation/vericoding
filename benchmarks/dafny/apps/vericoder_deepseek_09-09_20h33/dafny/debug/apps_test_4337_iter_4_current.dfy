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
    // ValidInput ensures at least 'P', 'W', 'G' are present
    // and all colors are in {'P', 'W', 'G', 'Y'}
    // So distinct colors must be between 3 and 4
    var distinct := DistinctColors(colors);
    assert distinct >= {'P', 'W', 'G'};
    assert distinct <= {'P', 'W', 'G', 'Y'};
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
        assert distinctColors == {'P', 'W', 'G'};
        result := "Three";
    } else {
        assert distinctColors == {'P', 'W', 'G', 'Y'};
        result := "Four";
    }
}
// </vc-code>

