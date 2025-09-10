predicate ValidInput(n: int, segments: seq<(int, int)>)
{
    n >= 1 && |segments| == n && 
    forall i :: 0 <= i < n ==> segments[i].0 <= segments[i].1
}

predicate CoversAll(segments: seq<(int, int)>, idx: int)
{
    0 <= idx < |segments| &&
    forall j :: 0 <= j < |segments| ==> 
        segments[idx].0 <= segments[j].0 && segments[j].1 <= segments[idx].1
}

predicate HasMinLeftAndMaxRight(segments: seq<(int, int)>, idx: int)
{
    0 <= idx < |segments| &&
    (forall j :: 0 <= j < |segments| ==> segments[idx].0 <= segments[j].0) &&
    (forall j :: 0 <= j < |segments| ==> segments[idx].1 >= segments[j].1)
}

function MinLeft(segments: seq<(int, int)>): int
    requires |segments| > 0
{
    if |segments| == 1 then segments[0].0
    else if segments[0].0 <= MinLeft(segments[1..]) then segments[0].0
    else MinLeft(segments[1..])
}

function MaxRight(segments: seq<(int, int)>): int
    requires |segments| > 0
{
    if |segments| == 1 then segments[0].1
    else if segments[0].1 >= MaxRight(segments[1..]) then segments[0].1
    else MaxRight(segments[1..])
}

// <vc-helpers>
predicate MaxRightCovers(segments: seq<(int, int)>, idx: int)
{
    0 <= idx < |segments| &&
    (forall j :: 0 <= j < |segments| ==> segments[j].1 <= segments[idx].1)
}

predicate MinLeftCovers(segments: seq<(int, int)>, idx: int)
{
    0 <= idx < |segments| &&
    (forall j :: 0 <= j < |segments| ==> segments[idx].0 <= segments[j].0)
}
// </vc-helpers>

// <vc-spec>
method solve(n: int, segments: seq<(int, int)>) returns (result: int)
    requires ValidInput(n, segments)
    ensures result == -1 || (1 <= result <= n)
    ensures result != -1 ==> 
        (var idx := result - 1;
         HasMinLeftAndMaxRight(segments, idx) &&
         CoversAll(segments, idx))
    ensures result == -1 ==> 
        !(exists i :: 0 <= i < n && HasMinLeftAndMaxRight(segments, i))
// </vc-spec>
// <vc-code>
{
    var minL := MinLeft(segments);
    var maxR := MaxRight(segments);

    for i := 0 to n - 1
        invariant 0 <= i <= n
        invariant ValidInput(n, segments)
        invariant MinLeft(segments) == minL
        invariant MaxRight(segments) == maxR
        invariant (forall k :: 0 <= k < i ==> !(HasMinLeftAndMaxRight(segments, k)))
    {
        if (segments[i].0 == minL && segments[i].1 == maxR) {
            // Need to prove that segments[i] is indeed the segment with min left and max right.
            // minL is the minimum of all .0 values, so segments[i].0 == minL implies segments[i].0 <= segments[j].0 for all j.
            // maxR is the maximum of all .1 values, so segments[i].1 == maxR implies segments[i].1 >= segments[j].1 for all j.
            // These two together satisfy HasMinLeftAndMaxRight(segments, i).
            // We also need to prove CoversAll(segments, i).
            // CoversAll(segments, i) requires segments[i].0 <= segments[j].0 && segments[j].1 <= segments[i].1 for all j.
            // We have segments[i].0 <= segments[j].0 from the definition of minL.
            // We have segments[j].1 <= segments[i].1 from the definition of maxR.
            // This proves CoversAll(segments, i).
            assert HasMinLeftAndMaxRight(segments, i) by {
                forall j | 0 <= j < |segments|
                ensures segments[i].0 <= segments[j].0 && segments[i].1 >= segments[j].1
                {
                    assert minL <= segments[j].0; // From definition of MinLeft
                    assert maxR >= segments[j].1; // From definition of MaxRight
                }
            }
            assert CoversAll(segments, i) by {
                forall j | 0 <= j < |segments|
                ensures segments[i].0 <= segments[j].0 && segments[j].1 <= segments[i].1
                {
                    assert minL <= segments[j].0;
                    assert maxR >= segments[j].1;
                }
            }
            return i + 1;
        }
    }
    // If we reach here, it means no segment satisfies HasMinLeftAndMaxRight.
    // By the loop invariant, for all k from 0 to n-1 (since we iterate up to n-1),
    // it's not the case that HasMinLeftAndMaxRight(segments, k) holds.
    // So, !(exists i :: 0 <= i < n && HasMinLeftAndMaxRight(segments, i)) is true.
    forall i | 0 <= i < n
        ensures !(HasMinLeftAndMaxRight(segments, i))
    {
        if (segments[i].0 == minL && segments[i].1 == maxR) {
            // This case is handled by the return inside the loop, so we won't reach here.
        } else {
            // If segments[i] is not (minL, maxR), then it cannot be the segment with MinLeft and MaxRight.
            // Because if it were, its left would be minL and its right would be maxR.
            // So, segments[i].0 != minL || segments[i].1 != maxR implies !HasMinLeftAndMaxRight(segments, i).
        }
    }
    return -1;
}
// </vc-code>

