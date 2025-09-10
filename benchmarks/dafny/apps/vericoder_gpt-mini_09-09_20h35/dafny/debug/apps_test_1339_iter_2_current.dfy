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
    } else {
        var rest := segments[1..];
        MinLeft_le_all(rest);
        var mrest := MinLeft(rest);
        if segments[0].0 <= mrest {
            assert MinLeft(segments) == segments[0].0;
            forall j | 0 <= j < |segments| {
                if j == 0 {
                    assert MinLeft(segments) <= segments[j].0;
                } else {
                    assert MinLeft(segments) == segments[0].0;
                    assert segments[0].0 <= mrest;
                    assert mrest <= segments[j].0;
                    assert MinLeft(segments) <= segments[j].0;
                }
            }
        } else {
            assert MinLeft(segments) == mrest;
            forall j | 0 <= j < |segments| {
                if j == 0 {
                    assert MinLeft(segments) <= segments[j].0;
                } else {
                    assert MinLeft(segments) == mrest;
                    assert mrest <= segments[j].0;
                    assert MinLeft(segments) <= segments[j].0;
                }
            }
        }
    }
}

lemma MaxRight_ge_all(segments: seq<(int,int)>)
    requires |segments| > 0
    ensures forall j :: 0 <= j < |segments| ==> MaxRight(segments) >= segments[j].1
    decreases |segments|
{
    if |segments| == 1 {
    } else {
        var rest := segments[1..];
        MaxRight_ge_all(rest);
        var rrest := MaxRight(rest);
        if segments[0].1 >= rrest {
            assert MaxRight(segments) == segments[0].1;
            forall j | 0 <= j < |segments| {
                if j == 0 {
                    assert MaxRight(segments) >= segments[j].1;
                } else {
                    assert rrest >= segments[j].1;
                    assert segments[0].1 >= rrest;
                    assert MaxRight(segments) >= segments[j].1;
                }
            }
        } else {
            assert MaxRight(segments) == rrest;
            forall j | 0 <= j < |segments| {
                if j == 0 {
                    assert MaxRight(segments) >= segments[j].1;
                } else {
                    assert MaxRight(segments) == rrest;
                    assert rrest >= segments[j].1;
                    assert MaxRight(segments) >= segments[j].1;
                }
            }
        }
    }
}

lemma ExistsIndexWithMinLeft(segments: seq<(int,int)>)
    requires |segments| > 0
    ensures exists i :: 0 <= i < |segments| && MinLeft(segments) == segments[i].0
    decreases |segments|
{
    if |segments| == 1 {
        assert MinLeft(segments) == segments[0].0;
        assert exists i :: 0 <= i < |segments| && MinLeft(segments) == segments[i].0;
    } else {
        var rest := segments[1..];
        ExistsIndexWithMinLeft(rest);
        var mrest := MinLeft(rest);
        if segments[0].0 <= mrest {
            assert MinLeft(segments) == segments[0].0;
            assert exists i :: 0 <= i < |segments| && MinLeft(segments) == segments[i].0;
        } else {
            // MinLeft(segments) == mrest and IH gives existence in rest,
            // which corresponds to an index + 1 in the original sequence.
            assert MinLeft(segments) == mrest;
            assert exists j :: 0 <= j < |rest| && mrest == rest[j].0;
            // From rest[j] == segments[j+1], we get existence in original
            assert exists k :: 0 <= k < |segments| && MinLeft(segments) == segments[k].0;
        }
    }
}

lemma ExistsIndexWithMaxRight(segments: seq<(int,int)>)
    requires |segments| > 0
    ensures exists i :: 0 <= i < |segments| && MaxRight(segments) == segments[i].1
    decreases |segments|
{
    if |segments| == 1 {
        assert MaxRight(segments) == segments[0].1;
        assert exists i :: 0 <= i < |segments| && MaxRight(segments) == segments[i].1;
    } else {
        var rest := segments[1..];
        ExistsIndexWithMaxRight(rest);
        var rrest := MaxRight(rest);
        if segments[0].1 >= rrest {
            assert MaxRight(segments) == segments[0].1;
            assert exists i :: 0 <= i < |segments| && MaxRight(segments) == segments[i].1;
        } else {
            assert MaxRight(segments) == rrest;
            assert exists j :: 0 <= j < |rest| && rrest == rest[j].1;
            assert exists k :: 0 <= k < |segments| && MaxRight(segments) == segments[k].1;
        }
    }
}

lemma HasMinLeftAndMaxRight_implies_equals(segments: seq<(int,int)>, idx: int)
    requires |segments| > 0
    requires 0 <= idx < |segments|
    ensures HasMinLeftAndMaxRight(segments, idx) ==> (segments[idx].0 == MinLeft(segments) && segments[idx].1 == MaxRight(segments))
{
    MinLeft_le_all(segments);
    MaxRight_ge_all(segments);
    ExistsIndexWithMinLeft(segments);
    ExistsIndexWithMaxRight(segments);
    if !HasMinLeftAndMaxRight(segments, idx) {
        // vacuously true
    } else {
        // From MinLeft_le_all we have MinLeft <= segments[idx].0
        assert MinLeft(segments) <= segments[idx].0;
        // From ExistsIndexWithMinLeft there exists k with MinLeft == segments[k].0
        assert exists k :: 0 <= k < |segments| && MinLeft(segments) == segments[k].0;
        // From HasMinLeftAndMaxRight: segments[idx].0 <= segments[k].0 == MinLeft
        // Therefore segments[idx].0 <= MinLeft
        // Combining gives equality
        // The solver can combine these facts; assert the equalities explicitly:
        // pick such a k via existential reasoning:
        assert forall k :: 0 <= k < |segments| && MinLeft(segments) == segments[k].0 ==> segments[idx].0 <= MinLeft(segments);
        assert segments[idx].0 <= MinLeft(segments);
        assert segments[idx].0 == MinLeft(segments);

        // Similarly for MaxRight
        assert MaxRight(segments) >= segments[idx].1;
        assert exists k :: 0 <= k < |segments| && MaxRight(segments) == segments[k].1;
        assert forall k :: 0 <= k < |segments| && MaxRight(segments) == segments[k].1 ==> segments[idx].1 >= MaxRight(segments);
        assert segments[idx].1 >= MaxRight(segments);
        assert segments[idx].1 == MaxRight(segments);
    }
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
    result := -1;
    return;
}
// </vc-code>

