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
lemma Distinct_subset_allowed(colors: seq<char>)
    requires (forall c :: c in colors ==> c in {'P','W','G','Y'})
    ensures DistinctColors(colors) <= {'P','W','G','Y'}
{
    var s := DistinctColors(colors);
    // For an arbitrary element of s, it is an element of colors by definition,
    // and thus by the require is in the allowed set.
    forall c | c in s
        ensures c in {'P','W','G','Y'}
    {
        // c in s means c in colors because s = set c | c in colors
        assert c in colors;
        assert c in {'P','W','G','Y'};
    }
}

lemma Has_PWG_subset(colors: seq<char>)
    requires 'P' in colors && 'W' in colors && 'G' in colors
    ensures {'P','W','G'} <= DistinctColors(colors)
{
    var s := DistinctColors(colors);
    // Each of 'P','W','G' is in colors, hence in the distinct set s
    assert 'P' in s;
    assert 'W' in s;
    assert 'G' in s;
    assert {'P','W','G'} <= s;
}

lemma DistinctCountIs3or4(n: int, colors: seq<char>)
    requires ValidInput(n, colors)
    ensures |DistinctColors(colors)| == 3 || |DistinctColors(colors)| == 4
{
    var s := DistinctColors(colors);
    // s is subset of the four allowed colors
    Distinct_subset_allowed(colors);
    assert s <= {'P','W','G','Y'};
    assert |s| <= 4;

    // s contains 'P','W','G'
    Has_PWG_subset(colors);
    assert {'P','W','G'} <= s;
    assert 3 <= |s|;

    // Thus |s| is 3 or 4
    if |s| == 3 {
    } else {
        // Since |s| >= 3 and <= 4, the only other possibility is 4
        assert |s| == 4;
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
  var s := DistinctColors(colors);
  DistinctCountIs3or4(n, colors);
  if |s| == 3 {
    result := SolutionString(3);
  } else {
    // From the lemma we know |s| == 3 || |s| == 4, and here it is not 3, so it must be 4
    result := SolutionString(4);
  }
}
// </vc-code>

