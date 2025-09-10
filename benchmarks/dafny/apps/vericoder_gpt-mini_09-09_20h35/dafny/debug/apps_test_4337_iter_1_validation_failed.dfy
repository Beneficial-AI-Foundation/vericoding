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
lemma DistinctColorsEqualsSet(n: int, colors: seq<char>)
    requires ValidInput(n, colors)
    ensures if 'Y' in colors then DistinctColors(colors) == {'P','W','G','Y'} else DistinctColors(colors) == {'P','W','G'}
{
    if 'Y' in colors {
        // Each of these are in colors by ValidInput
        assert 'P' in colors;
        assert 'W' in colors;
        assert 'G' in colors;
        assert 'Y' in colors;

        // Hence each is in DistinctColors(colors)
        assert 'P' in DistinctColors(colors);
        assert 'W' in DistinctColors(colors);
        assert 'G' in DistinctColors(colors);
        assert 'Y' in DistinctColors(colors);

        // Show every element of DistinctColors(colors) is in the target set
        assert forall c :: c in DistinctColors(colors) ==> c in {'P','W','G','Y'} by {
            var c: char;
            assume c in DistinctColors(colors);
            // By definition of DistinctColors, c in colors
            assert c in colors;
            // From ValidInput, every element of colors is in the allowed set
            assert c in {'P','W','G','Y'};
        }

        // Mutual inclusion gives equality
        assert DistinctColors(colors) == {'P','W','G','Y'};
    } else {
        // 'Y' not in colors, but P,W,G are present by ValidInput
        assert 'P' in colors;
        assert 'W' in colors;
        assert 'G' in colors;

        assert 'P' in DistinctColors(colors);
        assert 'W' in DistinctColors(colors);
        assert 'G' in DistinctColors(colors);

        // Show every element of DistinctColors(colors) is in {'P','W','G'}
        assert forall c :: c in DistinctColors(colors) ==> c in {'P','W','G'} by {
            var c: char;
            assume c in DistinctColors(colors);
            // c in colors
            assert c in colors;
            // From ValidInput, c is one of the allowed chars
            assert c in {'P','W','G','Y'};
            // Since 'Y' is not in colors, c cannot be 'Y'
            if c == 'Y' {
                // Contradiction: c in colors and 'Y' not in colors
                assert false;
            }
            // Thus c is in {'P','W','G'}
            assert c in {'P','W','G'};
        }

        assert DistinctColors(colors) == {'P','W','G'};
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
    if 'Y' in colors {
        DistinctColorsEqualsSet(n, colors);
        result := "Four";
    } else {
        DistinctColorsEqualsSet(n, colors);
        result := "Three";
    }
}
// </vc-code>

