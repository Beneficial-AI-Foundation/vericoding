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
lemma DistinctColorsCharacters(colors: seq<char>)
    ensures forall c :: c in DistinctColors(colors) <==> c in set(colors)
{
    // This lemma is implicitly true by the definition of DistinctColors and set comprehension.
    // No explicit proof steps are needed for simple set equivalence if the definitions align.
}

lemma DistinctColorsCount(n: int, colors: seq<char>)
    requires ValidInput(n, colors)
    ensures var distinctColors := DistinctColors(colors);
            (distinctColors.Count == 3 || distinctColors.Count == 4)
    proof {
        var distinctColors := DistinctColors(colors);
        // From ValidInput: 'P' in colors, 'W' in colors, 'G' in colors
        // So {'P', 'W', 'G'} is a subset of distinctColors.
        assert 'P' in distinctColors;
        assert 'W' in distinctColors;
        assert 'G' in distinctColors;
        assert {'P', 'W', 'G'} <= distinctColors;
        assert distinctColors.Count >= 3; // At least P, W, G are present

        // From ValidInput: c in {'P', 'W', 'G', 'Y'} for all c in colors
        // So distinctColors can only contain elements from {'P', 'W', 'G', 'Y'}
        assert distinctColors <= {'P', 'W', 'G', 'Y'};
        assert distinctColors.Count <= 4; // At most P, W, G, Y can be present

        // Combining the above, 3 <= distinctColors.Count <= 4
        assert distinctColors.Count == 3 || distinctColors.Count == 4;
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
    // Prove that the distinct color count is either 3 or 4
    DistinctColorsCount(n, colors);
    if distinctColors.Count == 3 {
        result := "Three";
    } else { // distinctColors.Count must be 4 based on the lemma
        result := "Four";
    }
}
// </vc-code>

