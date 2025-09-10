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
lemma MinLeftProperty(segments: seq<(int, int)>)
    requires |segments| > 0
    ensures forall i :: 0 <= i < |segments| ==> MinLeft(segments) <= segments[i].0
    ensures exists i :: 0 <= i < |segments| && MinLeft(segments) == segments[i].0
{
    if |segments| == 1 {
        assert segments[0].0 == MinLeft(segments);
    } else {
        MinLeftProperty(segments[1..]);
        if segments[0].0 <= MinLeft(segments[1..]) {
            assert MinLeft(segments) == segments[0].0;
            forall i {:trigger segments[i].0} | 0 <= i < |segments| ensures MinLeft(segments) <= segments[i].0 {
                if i == 0 {
                    assert MinLeft(segments) == segments[0].0;
                } else {
                    assert MinLeft(segments) <= MinLeft(segments[1..]);
                    assert MinLeft(segments[1..]) <= segments[i].0;
                }
            }
        } else {
            assert MinLeft(segments) == MinLeft(segments[1..]);
            forall i {:trigger segments[i].0} | 0 <= i < |segments| ensures MinLeft(segments) <= segments[i].0 {
                if i == 0 {
                    assert MinLeft(segments) <= segments[0].0;
                } else {
                    assert MinLeft(segments) <= segments[i].0;
                }
            }
            var j :| 0 <= j < |segments[1..]| && MinLeft(segments[1..]) == segments[1..][j].0;
            assert MinLeft(segments) == segments[1..][j].0;
        }
    }
}

lemma MaxRightProperty(segments: seq<(int, int)>)
    requires |segments| > 0
    ensures forall i :: 0 <= i < |segments| ==> MaxRight(segments) >= segments[i].1
    ensures exists i :: 0 <= i < |segments| && MaxRight(segments) == segments[i].1
{
    if |segments| == 1 {
        assert segments[0].1 == MaxRight(segments);
    } else {
        MaxRightProperty(segments[1..]);
        if segments[0].1 >= MaxRight(segments[1..]) {
            assert MaxRight(segments) == segments[0].1;
            forall i {:trigger segments[i].1} | 0 <= i < |segments| ensures MaxRight(segments) >= segments[i].1 {
                if i == 0 {
                    assert MaxRight(segments) == segments[0].1;
                } else {
                    assert MaxRight(segments) >= MaxRight(segments[1..]);
                    assert MaxRight(segments[1..]) >= segments[i].1;
                }
            }
        } else {
            assert MaxRight(segments) == MaxRight(segments[1..]);
            forall i {:trigger segments[i].1} | 0 <= i < |segments| ensures MaxRight(segments) >= segments[i].1 {
                if i == 0 {
                    assert MaxRight(segments) >= segments[0].1;
                } else {
                    assert MaxRight(segments) >= segments[i].1;
                }
            }
            var j :| 0 <= j < |segments[1..]| && MaxRight(segments[1..]) == segments[1..][j].1;
            assert MaxRight(segments) == segments[1..][j].1;
        }
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
    MinLeftProperty(segments);
    MaxRightProperty(segments);

    for i := 0 to |segments|
        invariant forall j :: 0 <= j < i ==> segments[j].0 != minL || segments[j].1 != maxR
    {
        if segments[i].0 == minL && segments[i].1 == maxR {
            return i+1;
        }
    }
    return -1;
}
// </vc-code>

