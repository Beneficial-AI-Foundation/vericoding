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
lemma MinLeft_le_all(segments: seq<(int,int)>)
    requires |segments| > 0
    ensures forall j :: 0 <= j < |segments| ==> MinLeft(segments) <= segments[j].0
    decreases |segments|
{
    if |segments| == 1 {
        // MinLeft(segments) == segments[0].0, trivial
    } else {
        MinLeft_le_all(segments[1..]);
        var m := MinLeft(segments[1..]);
        if segments[0].0 <= m {
            assert MinLeft(segments) == segments[0].0;
            // for j = 0
            assert MinLeft(segments) <= segments[0].0;
            // for j >= 1 use recursive fact and segments[0].0 <= m <= segments[j].0
            assert forall j :: 1 <= j < |segments| ==> MinLeft(segments) <= segments[j].0
                by {
                    var j0 := j;
                    // m <= segments[j0].0 from recursive lemma applied to segments[1..]
                    assert MinLeft(segments[1..]) <= segments[j0 - 1].0;
                    // relate indices: segments[j0].0 == segments[1..][j0-1].0
                    assert segments[j0].0 == segments[1..][j0 - 1].0;
                    // segments[0].0 <= m
                    assert segments[0].0 <= MinLeft(segments[1..]);
                    calc {
                        MinLeft(segments);
                        <= { assert MinLeft(segments) == segments[0].0; }
                        segments[0].0;
                        <= { assert segments[0].0 <= MinLeft(segments[1..]); }
                        MinLeft(segments[1..]);
                        <= { assert MinLeft(segments[1..]) <= segments[1..][j0 - 1].0; }
                        segments[1..][j0 - 1].0;
                        == { assert segments[1..][j0 - 1].0 == segments[j0].0; }
                        segments[j0].0;
                    }
                }
        } else {
            // MinLeft(segments) == MinLeft(segments[1..]) == m
            assert MinLeft(segments) == m;
            // For j >= 1, use recursive lemma directly (index shift)
            assert forall j :: 1 <= j < |segments| ==> MinLeft(segments) <= segments[j].0
                by {
                    var j0 := j;
                    assert MinLeft(segments) == MinLeft(segments[1..]);
                    // From recursive lemma: MinLeft(segments[1..]) <= segments[1..][j0-1].0
                    assert MinLeft(segments[1..]) <= segments[1..][j0 - 1].0;
                    assert segments[j0].0 == segments[1..][j0 - 1].0;
                }
            // For j = 0: MinLeft(segments) == m <= segments[0].0 because m < segments[0].0 in this branch
            assert MinLeft(segments) <= segments[0].0;
        }
        // Combine to full forall
        assert forall j :: 0 <= j < |segments| ==> MinLeft(segments) <= segments[j].0;
    }
}

lemma MaxRight_ge_all(segments: seq<(int,int)>)
    requires |segments| > 0
    ensures forall j :: 0 <= j < |segments| ==> MaxRight(segments) >= segments[j].1
    decreases |segments|
{
    if |segments| == 1 {
        // trivial
    } else {
        MaxRight_ge_all(segments[1..]);
        var M := MaxRight(segments[1..]);
        if segments[0].1 >= M {
            assert MaxRight(segments) == segments[0].1;
            // j = 0
            assert MaxRight(segments) >= segments[0].1;
            // j >= 1: segments[0].1 >= M >= segments[j].1
            assert forall j :: 1 <= j < |segments| ==> MaxRight(segments) >= segments[j].1
                by {
                    var j0 := j;
                    assert MaxRight(segments) == segments[0].1;
                    assert segments[0].1 >= MaxRight(segments[1..]);
                    assert MaxRight(segments[1..]) >= segments[1..][j0 - 1].1;
                    assert segments[j0].1 == segments[1..][j0 - 1].1;
                }
        } else {
            assert MaxRight(segments) == MaxRight(segments[1..]);
            // j >= 1 by recursive lemma
            assert forall j :: 1 <= j < |segments| ==> MaxRight(segments) >= segments[j].1
                by {
                    var j0 := j;
                    assert MaxRight(segments) == MaxRight(segments[1..]);
                    assert MaxRight(segments[1..]) >= segments[1..][j0 - 1].1;
                    assert segments[j0].1 == segments[1..][j0 - 1].1;
                }
            // j = 0: MaxRight(segments) >= segments[0].1 because M > segments[0].1 in this branch, but MaxRight==M, so M >= segments[0].1
            assert MaxRight(segments) >= segments[0].1;
        }
        assert forall j :: 0 <= j < |segments| ==> MaxRight(segments) >= segments[j].1;
    }
}

lemma MinLeft_is_in_seq(segments: seq<(int,int)>)
    requires |segments| > 0
    ensures exists k :: 0 <= k < |segments| && MinLeft(segments) == segments[k].0
    decreases |segments|
{
    if |segments| == 1 {
        reveal MinLeft;
        assert MinLeft(segments) == segments[0].0;
        exists 0;
    } else {
        MinLeft_is_in_seq(segments[1..]);
        var m := MinLeft(segments[1..]);
        if segments[0].0 <= m {
            assert MinLeft(segments) == segments[0].0;
            exists 0;
        } else {
            // MinLeft(segments) == MinLeft(segments[1..]) and the witness shifts by +1
            var k':| 0 <= k' < |segments[1..]| && MinLeft(segments[1..]) == segments[1..][k'].0;
            // obtain k' from the existential produced by the recursive lemma
            // We can directly pattern-match by calling the lemma into a witness
            var found := MinLeft(segments[1..]); // dummy to help extraction
            // Instead use a direct approach: use recursive lemma's ensures
            MinLeft_is_in_seq(segments[1..]);
            var w :| 0 <= w < |segments[1..]| && MinLeft(segments[1..]) == segments[1..][w].0;
            exists w + 1;
        }
    }
}

lemma MaxRight_is_in_seq(segments: seq<(int,int)>)
    requires |segments| > 0
    ensures exists k :: 0 <= k < |segments| && MaxRight(segments) == segments[k].1
    decreases |segments|
{
    if |segments| == 1 {
        reveal MaxRight;
        assert MaxRight(segments) == segments[0].1;
        exists 0;
    } else {
        MaxRight_is_in_seq(segments[1..]);
        var M := MaxRight(segments[1..]);
        if segments[0].1 >= M {
            assert MaxRight(segments) == segments[0].1;
            exists 0;
        } else {
            MaxRight_is_in_seq(segments[1..]);
            var w :| 0 <= w < |segments[1..]| && MaxRight(segments[1..]) == segments[1..][w].1;
            exists w + 1;
        }
    }
}

lemma HasMinLeftAndMaxRight_implies_equals(segments: seq<(int,int)>, idx: int)
    requires |segments| > 0
    requires 0 <= idx < |segments|
    requires HasMinLeftAndMaxRight(segments, idx)
    ensures segments[idx].0 == MinLeft(segments)
    ensures segments[idx].1 == MaxRight(segments)
{
    // Left equality
    MinLeft_le_all(segments);
    MinLeft_is_in_seq(segments);
    var k :| 0 <= k < |segments| && MinLeft(segments) == segments[k].0;
    // From HasMinLeftAndMaxRight we have segments[idx].0 <= segments[k].0 == MinLeft
    assert forall j :: 0 <= j < |segments| ==> segments[idx].0 <= segments[j].0;
    assert segments[idx].0 <= segments[k].0;
    // From MinLeft_le_all we have MinLeft <= segments[idx].0
    assert MinLeft(segments) <= segments[idx].0;
    // combine to equality
    assert segments[idx].0 == MinLeft(segments);

    // Right equality
    MaxRight_ge_all(segments);
    MaxRight_is_in_seq(segments);
    var k2 :| 0 <= k2 < |segments| && MaxRight(segments) == segments[k2].1;
    assert forall j :: 0 <= j < |segments| ==> segments[idx].1 >= segments[j].1;
    assert segments[idx].1 >= segments[k2].1;
    assert MaxRight(segments) >= segments[idx].1;
    assert segments[idx].1 == MaxRight(segments);
}

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

