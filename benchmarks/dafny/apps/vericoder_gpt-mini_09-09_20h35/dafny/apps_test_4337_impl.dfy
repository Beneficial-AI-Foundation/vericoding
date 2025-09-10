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
    forall c | c in DistinctColors(colors)
        ensures c in {'P','W','G','Y'}
    {
        // By definition of DistinctColors, any element of DistinctColors(colors) is in colors
        assert c in colors;
        assert c in {'P','W','G','Y'};
    }
}

lemma Has_PWG_subset(colors: seq<char>)
    requires 'P' in colors && 'W' in colors && 'G' in colors
    ensures {'P','W','G'} <= DistinctColors(colors)
{
    assert 'P' in DistinctColors(colors);
    assert 'W' in DistinctColors(colors);
    assert 'G' in DistinctColors(colors);
    assert {'P','W','G'} <= DistinctColors(colors);
}

lemma DistinctCountIs3or4(n: int, colors: seq<char>)
    requires ValidInput(n, colors)
    ensures |DistinctColors(colors)| == 3 || |DistinctColors(colors)| == 4
{
    var s := DistinctColors(colors);

    // s is subset of the four allowed colors
    Distinct_subset_allowed(colors);
    assert s <= {'P','W','G','Y'};

    // s contains 'P','W','G'
    Has_PWG_subset(colors);
    assert {'P','W','G'} <= s;

    // Case split on whether 'Y' is present in s
    if 'Y' in s {
        // s contains P,W,G and Y, and is subset of the allowed four, so it equals the allowed four
        assert 'P' in s;
        assert 'W' in s;
        assert 'G' in s;
        assert 'Y' in s;
        // Show that {'P','W','G','Y'} <= s
        forall c | c in {'P','W','G','Y'}
            ensures c in s
        {
            if c == 'Y' {
                assert c in s;
            } else if c == 'P' {
                assert c in s;
            } else if c == 'W' {
                assert c in s;
            } else {
                assert c in s;
            }
        }
        // And s <= {'P','W','G','Y'} holds from above
        assert s == {'P','W','G','Y'};
        assert |s| == 4;
    } else {
        // Y not in s. Since s <= {'P','W','G','Y'}, every element of s must be one of P,W,G
        forall c | c in s
            ensures c in {'P','W','G'}
        {
            // c in s implies c in colors (by definition of DistinctColors)
            assert c in colors;
            // From ValidInput we know colors elements are among allowed
            assert c in {'P','W','G','Y'};
            // And since Y not in s and c in s, c != 'Y'
            assert c != 'Y';
            // Thus c is in {'P','W','G'}
            assert c in {'P','W','G'};
        }
        assert s <= {'P','W','G'};
        // Since we also have {'P','W','G'} <= s, equality follows
        assert {'P','W','G'} <= s;
        assert s <= {'P','W','G'};
        assert s == {'P','W','G'};
        assert |s| == 3;
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
    result := SolutionString(4);
  }
}
// </vc-code>

