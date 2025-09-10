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
lemma DistinctColorsCount(colors: seq<char>)
    requires ValidInput(|colors|, colors)
    ensures var distinctColors := DistinctColors(colors);
            |distinctColors| == 3 || |distinctColors| == 4
{
    var distinctColors := DistinctColors(colors);
    
    // From ValidInput, we know P, W, G are in colors
    assert 'P' in distinctColors;
    assert 'W' in distinctColors;
    assert 'G' in distinctColors;
    
    // So we have at least 3 distinct colors
    assert |distinctColors| >= 3;
    
    // All colors are from {'P', 'W', 'G', 'Y'}
    assert distinctColors <= {'P', 'W', 'G', 'Y'};
    
    // So we have at most 4 distinct colors
    assert |distinctColors| <= 4;
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
    var distinctColors := DistinctColors(colors);
    
    DistinctColorsCount(colors);
    
    if |distinctColors| == 3 {
        result := "Three";
    } else {
        result := "Four";
    }
}
// </vc-code>

