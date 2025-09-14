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
lemma DistinctColorsCardinality(colors: seq<char>)
    requires ValidInput(|colors|, colors)
    ensures var distinctColors := DistinctColors(colors);
            |distinctColors| == 3 || |distinctColors| == 4
    ensures var distinctColors := DistinctColors(colors);
            |distinctColors| == 3 <==> 'Y' !in colors
    ensures var distinctColors := DistinctColors(colors);
            |distinctColors| == 4 <==> 'Y' in colors
{
    var distinctColors := DistinctColors(colors);
    
    assert 'P' in distinctColors;
    assert 'W' in distinctColors;
    assert 'G' in distinctColors;
    
    if 'Y' in colors {
        assert 'Y' in distinctColors;
        assert distinctColors >= {'P', 'W', 'G', 'Y'};
        assert forall c | c in distinctColors :: c in {'P', 'W', 'G', 'Y'};
        assert distinctColors == {'P', 'W', 'G', 'Y'};
        assert |distinctColors| == 4;
    } else {
        assert 'Y' !in distinctColors;
        assert distinctColors <= {'P', 'W', 'G'};
        assert distinctColors >= {'P', 'W', 'G'};
        assert distinctColors == {'P', 'W', 'G'};
        assert |distinctColors| == 3;
    }
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
    DistinctColorsCardinality(colors);
    
    if 'Y' in colors {
        result := "Four";
    } else {
        result := "Three";
    }
}
// </vc-code>

