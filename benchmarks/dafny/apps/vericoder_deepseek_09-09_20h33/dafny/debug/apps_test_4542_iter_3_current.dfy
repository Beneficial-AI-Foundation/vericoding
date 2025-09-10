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
lemma CountSegmentsLemma(s: string, i: int)
    requires ValidInput(s)
    requires 0 <= i < |s| - 1
    ensures CountSegments(s[..i+1]) == CountSegments(s[..i]) + (if s[i] != s[i-1] && i > 0 then 1 else 0)
{
}

lemma CountSegmentsBase(s: string)
    requires ValidInput(s)
    ensures CountSegments(s[..1]) == 1
{
    assert |s[..1]| == 1;
}

lemma CountSegmentsStep(s: string, i: int)
    requires ValidInput(s)
    requires 1 <= i < |s|
    ensures CountSegments(s[..i+1]) == CountSegments(s[..i]) + (if s[i] != s[i-1] then 1 else 0)
{
    if i == 1 {
        if s[1] != s[0] {
            assert CountSegments(s[..2]) == 2;
            assert CountSegments(s[..1]) == 1;
        } else {
            assert CountSegments(s[..2]) == 1;
            assert CountSegments(s[..1]) == 1;
        }
    } else {
        CountSegmentsStep(s[..i], i-1);
        var prefix := s[..i];
        assert prefix[..i] == prefix;
        if s[i] != s[i-1] {
            assert CountSegments(s[..i+1]) == CountSegments(prefix) + 1;
        } else {
            assert CountSegments(s[..i+1]) == CountSegments(prefix);
        }
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
    var count := 0;
    var i := 1;
    
    if |s| == 1 {
        result := 0;
        return;
    }
    
    assert CountSegments(s[..1]) == 1;
    
    while i < |s|
        invariant 1 <= i <= |s|
        invariant count == CountSegments(s[..i]) - 1
        invariant count >= 0
        invariant count <= i - 1
    {
        CountSegmentsStep(s, i);
        if s[i] != s[i-1] {
            count := count + 1;
        }
        i := i + 1;
    }
    result := count;
}
// </vc-code>

