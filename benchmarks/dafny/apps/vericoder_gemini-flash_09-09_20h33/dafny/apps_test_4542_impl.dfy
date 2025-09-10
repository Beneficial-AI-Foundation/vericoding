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
function CountSegmentsHelper(s: string, currentIndex: int): int
    requires 0 <= currentIndex < |s|
    requires |s| > 0
    ensures CountSegmentsHelper(s, currentIndex) >= 1
    ensures CountSegmentsHelper(s, currentIndex) <= currentIndex + 1
    decreases currentIndex
{
    if currentIndex == 0 then 1
    else
        CountSegmentsHelper(s, currentIndex - 1) + (if s[currentIndex] != s[currentIndex - 1] then 1 else 0)
}

lemma CountSegmentsRecurrence(s: string)
    requires |s| > 0
    ensures forall k :: 0 <= k < |s| ==> CountSegments(s[..k+1]) == CountSegmentsHelper(s, k)
{
    forall k | 0 <= k < |s|
        ensures CountSegments(s[..k+1]) == CountSegmentsHelper(s, k)
    {
        if k == 0 {
            assert CountSegments(s[..1]) == 1;
            assert CountSegmentsHelper(s, 0) == 1;
        } else {
            CountSegmentsRecurrence(s[..k]); // Inductive hypothesis for s[..k]

            calc {
                CountSegments(s[..k+1]);
                {
                    assert k+1 > 0;
                    assert k+1 <= |s|;
                }
                CountSegments(s[..k]) + (if s[k] != s[k-1] then 1 else 0);
                {
                    assert CountSegments(s[..k]) == CountSegmentsHelper(s, k-1) by {
                        if k > 0 { // Correctly apply induction hypothesis for s[..k] which has length k
                             CountSegmentsRecurrence(s);
                        }
                    }
                }
                (CountSegmentsHelper(s, k-1) + (if s[k] != s[k-1] then 1 else 0));
                CountSegmentsHelper(s, k);
            }
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
    result := 0;
    if |s| == 1 {
        result := 0;
    } else {
        var currentSegments := 1;
        var i := 1;
        CountSegmentsRecurrence(s); // Establish the connection between specification and helper
        while i < |s|
            invariant 1 <= i <= |s|
            invariant currentSegments == CountSegmentsHelper(s, i - 1)
            invariant currentSegments == CountSegments(s[..i]) // This seems to be the crucial part
        {
            if s[i] != s[i-1] {
                currentSegments := currentSegments + 1;
            }
            i := i + 1;
        }
        result := currentSegments - 1;
    }
}
// </vc-code>

