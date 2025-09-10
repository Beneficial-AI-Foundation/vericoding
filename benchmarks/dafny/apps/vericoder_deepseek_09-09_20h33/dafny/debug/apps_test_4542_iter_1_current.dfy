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
    ensures CountSegments(s[..i+1]) == CountSegments(s[..i]) + (if s[i] != s[i+1] then 1 else 0)
{
}

lemma CountSegmentsBase(s: string)
    requires ValidInput(s)
    ensures CountSegments(s[..1]) == 1
{
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
    var i := 0;
    while i < |s| - 1
        invariant 0 <= i <= |s| - 1
        invariant count == CountSegments(s[..i+1]) - 1
        invariant count >= 0
        invariant count <= i
    {
        if s[i] != s[i+1] {
            count := count + 1;
        }
        i := i + 1;
    }
    result := count;
}
// </vc-code>

