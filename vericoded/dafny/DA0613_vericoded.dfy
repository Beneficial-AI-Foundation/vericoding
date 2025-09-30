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
lemma CountSegmentsProperty(s: string, i: int)
    requires |s| > 0
    requires 0 < i <= |s|
    ensures CountSegments(s[..i]) >= 1
    ensures CountSegments(s[..i]) <= i
{
    if i == 1 {
        assert s[..1] == s[..1];
    } else {
        CountSegmentsProperty(s, i-1);
        assert s[..i][..i-1] == s[..i-1];
    }
}

lemma CountSegmentsExtend(s: string, i: int)
    requires |s| > 0
    requires 0 < i < |s|
    ensures CountSegments(s[..i+1]) == CountSegments(s[..i]) + (if s[i] != s[i-1] then 1 else 0)
{
    assert s[..i+1][..i] == s[..i];
    assert s[..i+1][i] == s[i];
    assert s[..i+1][i-1] == s[i-1];
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
    var segments := 1;
    var i := 1;
    
    while i < |s|
        invariant 1 <= i <= |s|
        invariant segments == CountSegments(s[..i])
        invariant segments >= 1
        invariant segments <= i
    {
        CountSegmentsExtend(s, i);
        if s[i] != s[i-1] {
            segments := segments + 1;
        }
        i := i + 1;
    }
    
    assert s[..|s|] == s;
    result := segments - 1;
}
// </vc-code>

