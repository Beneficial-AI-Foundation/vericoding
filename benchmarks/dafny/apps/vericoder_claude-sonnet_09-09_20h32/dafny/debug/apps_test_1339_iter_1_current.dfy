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
lemma MinLeftIsMinimal(segments: seq<(int, int)>, i: int)
    requires |segments| > 0
    requires 0 <= i < |segments|
    ensures MinLeft(segments) <= segments[i].0
{
    if |segments| == 1 {
        assert segments[i] == segments[0];
    } else {
        if segments[0].0 <= MinLeft(segments[1..]) {
            if i == 0 {
                assert MinLeft(segments) == segments[0].0;
            } else {
                MinLeftIsMinimal(segments[1..], i-1);
                assert MinLeft(segments) == segments[0].0 <= segments[i].0;
            }
        } else {
            if i == 0 {
                MinLeftIsMinimal(segments[1..], 0);
                assert MinLeft(segments[1..]) < segments[0].0;
                assert MinLeft(segments) == MinLeft(segments[1..]) <= segments[1].0 == segments[i].0;
            } else {
                MinLeftIsMinimal(segments[1..], i-1);
            }
        }
    }
}

lemma MaxRightIsMaximal(segments: seq<(int, int)>, i: int)
    requires |segments| > 0
    requires 0 <= i < |segments|
    ensures MaxRight(segments) >= segments[i].1
{
    if |segments| == 1 {
        assert segments[i] == segments[0];
    } else {
        if segments[0].1 >= MaxRight(segments[1..]) {
            if i == 0 {
                assert MaxRight(segments) == segments[0].1;
            } else {
                MaxRightIsMaximal(segments[1..], i-1);
                assert MaxRight(segments) == segments[0].1 >= segments[i].1;
            }
        } else {
            if i == 0 {
                MaxRightIsMaximal(segments[1..], 0);
                assert MaxRight(segments[1..]) > segments[0].1;
                assert MaxRight(segments) == MaxRight(segments[1..]) >= segments[1].1 >= segments[i].1;
            } else {
                MaxRightIsMaximal(segments[1..], i-1);
            }
        }
    }
}

lemma MinLeftExists(segments: seq<(int, int)>)
    requires |segments| > 0
    ensures exists i :: 0 <= i < |segments| && segments[i].0 == MinLeft(segments)
{
    if |segments| == 1 {
        assert segments[0].0 == MinLeft(segments);
    } else {
        if segments[0].0 <= MinLeft(segments[1..]) {
            assert segments[0].0 == MinLeft(segments);
        } else {
            MinLeftExists(segments[1..]);
            var i :| 0 <= i < |segments[1..]| && segments[1..][i].0 == MinLeft(segments[1..]);
            assert segments[i+1].0 == MinLeft(segments[1..]) == MinLeft(segments);
        }
    }
}

lemma MaxRightExists(segments: seq<(int, int)>)
    requires |segments| > 0
    ensures exists i :: 0 <= i < |segments| && segments[i].1 == MaxRight(segments)
{
    if |segments| == 1 {
        assert segments[0].1 == MaxRight(segments);
    } else {
        if segments[0].1 >= MaxRight(segments[1..]) {
            assert segments[0].1 == MaxRight(segments);
        } else {
            MaxRightExists(segments[1..]);
            var i :| 0 <= i < |segments[1..]| && segments[1..][i].1 == MaxRight(segments[1..]);
            assert segments[i+1].1 == MaxRight(segments[1..]) == MaxRight(segments);
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
    var minLeft := MinLeft(segments);
    var maxRight := MaxRight(segments);
    
    MinLeftIsMinimal(segments, 0);
    MaxRightIsMaximal(segments, 0);
    
    var i := 0;
    while i < n
        invariant 0 <= i <= n
        invariant forall j :: 0 <= j < i ==> !(segments[j].0 == minLeft && segments[j].1 == maxRight)
    {
        if segments[i].0 == minLeft && segments[i].1 == maxRight {
            assert HasMinLeftAndMaxRight(segments, i) by {
                forall j | 0 <= j < |segments| 
                    ensures segments[i].0 <= segments[j].0 && segments[i].1 >= segments[j].1
                {
                    MinLeftIsMinimal(segments, j);
                    MaxRightIsMaximal(segments, j);
                }
            }
            assert CoversAll(segments, i);
            return i + 1;
        }
        i := i + 1;
    }
    
    assert forall j :: 0 <= j < n ==> !(segments[j].0 == minLeft && segments[j].1 == maxRight);
    assert !(exists j :: 0 <= j < n && HasMinLeftAndMaxRight(segments, j)) by {
        if exists j :: 0 <= j < n && HasMinLeftAndMaxRight(segments, j) {
            var j :| 0 <= j < n && HasMinLeftAndMaxRight(segments, j);
            forall k | 0 <= k < n 
                ensures segments[j].0 <= segments[k].0
            {
                MinLeftIsMinimal(segments, k);
            }
            forall k | 0 <= k < n 
                ensures segments[j].1 >= segments[k].1
            {
                MaxRightIsMaximal(segments, k);
            }
            MinLeftExists(segments);
            MaxRightExists(segments);
            var leftIdx :| 0 <= leftIdx < n && segments[leftIdx].0 == minLeft;
            var rightIdx :| 0 <= rightIdx < n && segments[rightIdx].1 == maxRight;
            assert segments[j].0 <= segments[leftIdx].0 == minLeft;
            assert segments[j].0 >= minLeft by { MinLeftIsMinimal(segments, j); }
            assert segments[j].0 == minLeft;
            assert segments[j].1 >= segments[rightIdx].1 == maxRight;
            assert segments[j].1 <= maxRight by { MaxRightIsMaximal(segments, j); }
            assert segments[j].1 == maxRight;
            assert false;
        }
    }
    
    return -1;
}
// </vc-code>

