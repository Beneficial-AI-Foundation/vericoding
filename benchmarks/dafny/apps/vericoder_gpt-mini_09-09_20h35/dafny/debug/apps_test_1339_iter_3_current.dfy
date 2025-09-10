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
lemma EqualsImpliesHasMinLeftAndMaxRight(segments: seq<(int,int)>, idx: int)
    requires |segments| > 0
    requires 0 <= idx < |segments|
    requires segments[idx].0 == MinLeft(segments)
    requires segments[idx].1 == MaxRight(segments)
    ensures HasMinLeftAndMaxRight(segments, idx)
{
    MinLeft_le_all(segments);
    MaxRight_ge_all(segments);
    // show left property
    assert forall j :: 0 <= j < |segments| ==> MinLeft(segments) <= segments[j].0;
    assert forall j :: 0 <= j < |segments| ==> segments[idx].0 <= segments[j].0;
    // show right property
    assert forall j :: 0 <= j < |segments| ==> MaxRight(segments) >= segments[j].1;
    assert forall j :: 0 <= j < |segments| ==> segments[idx].1 >= segments[j].1;
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
    // Use lemmas to obtain global facts about minL and maxR
    MinLeft_le_all(segments);
    MaxRight_ge_all(segments);

    var i := 0;
    // invariant: 0 <= i <= n, and no index < i satisfies both equalities
    while i < n
        invariant 0 <= i <= n
        invariant forall t :: 0 <= t < i ==> !(segments[t].0 == minL && segments[t].1 == maxR)
        decreases n - i
    {
        if segments[i].0 == minL && segments[i].1 == maxR {
            result := i + 1;
            return;
        }
        i := i + 1;
    }

    // If loop finished, no segment matches both minL and maxR
    // Prove that there is no index with HasMinLeftAndMaxRight
    if exists k :: 0 <= k < n && HasMinLeftAndMaxRight(segments, k) {
        var k0 :| 0 <= k0 < n && HasMinLeftAndMaxRight(segments, k0);
        HasMinLeftAndMaxRight_implies_equals(segments, k0);
        // segments[k0] must equal (minL, maxR), contradicting the loop invariant at exit (i == n)
        assert segments[k0].0 == minL && segments[k0].1 == maxR;
        // The loop invariant at exit states no t < n has both equalities
        assert forall t :: 0 <= t < n ==> !(segments[t].0 == minL && segments[t].1 == maxR);
        assert false;
    }

    result := -1;
    return;
}
// </vc-code>

