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
    assert 'P' in colors by { assert ValidInput(|colors|, colors); }
    assert 'W' in colors by { assert ValidInput(|colors|, colors); }
    assert 'G' in colors by { assert ValidInput(|colors|, colors); }
    
    // Therefore they are in distinctColors
    assert 'P' in distinctColors;
    assert 'W' in distinctColors;
    assert 'G' in distinctColors;
    
    // These three are distinct, so we have at least 3
    assert {'P', 'W', 'G'} <= distinctColors;
    assert |distinctColors| >= |{'P', 'W', 'G'}|;
    assert |{'P', 'W', 'G'}| == 3;
    assert |distinctColors| >= 3;
    
    // All colors in the input must be from {'P', 'W', 'G', 'Y'}
    assert forall c | c in colors :: c in {'P', 'W', 'G', 'Y'} by {
        assert ValidInput(|colors|, colors);
    }
    
    // Therefore distinctColors is a subset of {'P', 'W', 'G', 'Y'}
    assert forall c | c in distinctColors :: c in {'P', 'W', 'G', 'Y'} by {
        forall c | c in distinctColors
            ensures c in {'P', 'W', 'G', 'Y'}
        {
            assert c in colors;
        }
    }
    assert distinctColors <= {'P', 'W', 'G', 'Y'};
    
    // So we have at most 4 distinct colors
    assert |distinctColors| <= |{'P', 'W', 'G', 'Y'}|;
    assert |{'P', 'W', 'G', 'Y'}| == 4;
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

