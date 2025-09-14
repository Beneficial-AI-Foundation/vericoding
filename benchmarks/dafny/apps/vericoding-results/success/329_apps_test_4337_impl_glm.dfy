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
lemma DistinctCountLemma(colors: seq<char>)
    requires ValidInput(|colors|, colors)
    ensures |DistinctColors(colors)| == 3 || |DistinctColors(colors)| == 4
{
    var distinctColors := DistinctColors(colors);
    assert 'P' in distinctColors && 'W' in distinctColors && 'G' in distinctColors;
    assert forall c | c in distinctColors :: c in {'P','W','G','Y'};
    if 'Y' in distinctColors {
        assert {'P','W','G','Y'} <= distinctColors;
        assert distinctColors <= {'P','W','G','Y'};
        assert distinctColors == {'P','W','G','Y'};
        assert |distinctColors| == 4;
    } else {
        assert forall c | c in distinctColors :: c != 'Y';
        assert forall c | c in distinctColors :: c in {'P','W','G'};
        assert distinctColors <= {'P','W','G'};
        assert {'P','W','G'} <= distinctColors;
        assert distinctColors == {'P','W','G'};
        assert |distinctColors| == 3;
    }
    assert |distinctColors| >= 3;
    assert |distinctColors| <= 4;
    assert |distinctColors| == 3 || |distinctColors| == 4;
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
    var distinctCount := |distinctColors|;
    DistinctCountLemma(colors);
    result := SolutionString(distinctCount);
}
// </vc-code>

