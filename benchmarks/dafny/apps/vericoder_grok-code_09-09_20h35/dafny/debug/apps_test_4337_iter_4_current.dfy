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
lemma VerifyDistinctCount(colors: seq<char>)
    requires ValidInput(|colors|, colors)
    ensures |DistinctColors(colors)| == 3 || |DistinctColors(colors)| == 4
{
    var distinctColors := DistinctColors(colors);
    var s := distinctColors;
    if ('P' in s) { s := s - {'P'}; }
    if ('W' in s) { s := s - {'W'}; }
    if ('G' in s) { s := s - {'G'}; }
    assert |s| <= 1;
    assert |distinctColors| == 3 + |s|; 
    assert |s| == 0 || |s| == 1;
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
    var distinctCount := |DistinctColors(colors)|;
    VerifyDistinctCount(colors);
    assert distinctCount == 3 || distinctCount == 4;
    result := SolutionString(distinctCount);
}
// </vc-code>

