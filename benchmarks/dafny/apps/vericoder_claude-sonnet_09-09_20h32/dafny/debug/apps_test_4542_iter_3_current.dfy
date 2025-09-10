predicate ValidInput(s: string)
{
    |s| > 0 && forall i :: 0 <= i < |s| ==> s[i] == 'B' || s[i] == 'W'
}

function CountSegments(s: string): int
    requires |s| > 0
    ensures CountSegments(s) >= 1
    ensures CountSegments(s) <= |s|
{
    if |s| == 1 then 1
    else 
        CountSegments(s[..|s|-1]) + (if s[|s|-1] != s[|s|-2] then 1 else 0)
}

// <vc-helpers>
lemma CountSegmentsProperties(s: string)
    requires |s| > 0
    ensures CountSegments(s) >= 1
    ensures CountSegments(s) <= |s|
{
    if |s| == 1 {
        // Base case is trivial
    } else {
        CountSegmentsProperties(s[..|s|-1]);
    }
}

lemma CountSegmentsIterative(s: string, i: int, segments: int)
    requires |s| > 0
    requires 0 <= i <= |s|
    requires i == 0 ==> segments == 0
    requires i > 0 ==> segments == CountSegments(s[..i])
    ensures i == |s| ==> segments == CountSegments(s)
    decreases |s| - i
{
    if i == |s| {
        assert s[..i] == s;
    } else {
        var next_segments := segments + (if i == 0 || s[i] != s[i-1] then 1 else 0);
        CountSegmentsIncrementalLemma(s, i + 1, next_segments);
        CountSegmentsIterative(s, i + 1, next_segments);
    }
}

lemma CountSegmentsIncrementalLemma(s: string, i: int, segments: int)
    requires |s| > 0
    requires 1 <= i <= |s|
    requires i == 1 ==> segments == 1
    requires i > 1 ==> (segments == CountSegments(s[..i-1]) + (if s[i-1] != s[i-2] then 1 else 0))
    ensures segments == CountSegments(s[..i])
{
    if i == 1 {
        assert s[..1] == [s[0]];
        assert CountSegments(s[..1]) == 1;
    } else {
        assert s[..i] == s[..i-1] + [s[i-1]];
        assert CountSegments(s[..i]) == CountSegments(s[..i-1]) + (if s[i-1] != s[i-2] then 1 else 0);
    }
}
// </vc-helpers>

// <vc-spec>
method solve(s: string) returns (result: int)
    requires ValidInput(s)
    ensures result >= 0
    ensures result == CountSegments(s) - 1
    ensures result <= |s| - 1
// </vc-spec>
// <vc-code>
{
    if |s| == 1 {
        result := 0;
        return;
    }
    
    var segments := 1;
    var i := 1;
    
    while i < |s|
        invariant 1 <= i <= |s|
        invariant segments >= 1
        invariant segments == CountSegments(s[..i])
        invariant segments <= i
    {
        if s[i] != s[i-1] {
            segments := segments + 1;
        }
        if i + 1 == 1 {
            CountSegmentsIncrementalLemma(s, i + 1, segments);
        } else {
            CountSegmentsIncrementalLemma(s, i + 1, segments);
        }
        i := i + 1;
    }
    
    assert s[..i] == s;
    result := segments - 1;
}
// </vc-code>

