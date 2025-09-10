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
lemma MinLeftProperty(segments: seq<(int, int)>, i: int)
    requires |segments| > 0
    requires 0 <= i < |segments|
    ensures MinLeft(segments) <= segments[i].0
{
    if |segments| == 1 {
        assert i == 0;
    } else if i == 0 {
        if segments[0].0 <= MinLeft(segments[1..]) {
            // MinLeft(segments) == segments[0].0
        } else {
            // MinLeft(segments) == MinLeft(segments[1..])
            MinLeftProperty(segments[1..], 0);
        }
    } else {
        MinLeftProperty(segments[1..], i-1);
        if segments[0].0 <= MinLeft(segments[1..]) {
            // MinLeft(segments) == segments[0].0
        } else {
            // MinLeft(segments) == MinLeft(segments[1..])
        }
    }
}

lemma MaxRightProperty(segments: seq<(int, int)>, i: int)
    requires |segments| > 0
    requires 0 <= i < |segments|
    ensures MaxRight(segments) >= segments[i].1
{
    if |segments| == 1 {
        assert i == 0;
    } else if i == 0 {
        if segments[0].1 >= MaxRight(segments[1..]) {
            // MaxRight(segments) == segments[0].1
        } else {
            // MaxRight(segments) == MaxRight(segments[1..])
            MaxRightProperty(segments[1..], 0);
        }
    } else {
        MaxRightProperty(segments[1..], i-1);
        if segments[0].1 >= MaxRight(segments[1..]) {
            // MaxRight(segments) == segments[0].1
        } else {
            // MaxRight(segments) == MaxRight(segments[1..])
        }
    }
}

lemma CoversAllImpliesHasMinLeftAndMaxRight(segments: seq<(int, int)>, idx: int)
    requires |segments| > 0
    requires 0 <= idx < |segments|
    requires CoversAll(segments, idx)
    ensures HasMinLeftAndMaxRight(segments, idx)
{
    // If segment idx covers all others, then for all j:
    // segments[idx].0 <= segments[j].0 (min left)
    // segments[idx].1 >= segments[j].1 (max right)
}

lemma HasMinLeftAndMaxRightImpliesCoversAll(segments: seq<(int, int)>, idx: int)
    requires ValidInput(|segments|, segments)
    requires 0 <= idx < |segments|
    requires HasMinLeftAndMaxRight(segments, idx)
    ensures CoversAll(segments, idx)
{
    // If segment idx has min left and max right, and all segments are valid (left <= right),
    // then it covers all other segments
    forall j | 0 <= j < |segments|
    ensures segments[idx].0 <= segments[j].0 && segments[j].1 <= segments[idx].1
    {
        assert segments[idx].0 <= segments[j].0;  // from HasMinLeftAndMaxRight
        assert segments[idx].1 >= segments[j].1;  // from HasMinLeftAndMaxRight
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
    var minLeft := segments[0].0;
    var maxRight := segments[0].1;
    
    var i := 1;
    while i < n
        invariant 1 <= i <= n
        invariant minLeft == MinLeft(segments[0..i])
        invariant maxRight == MaxRight(segments[0..i])
    {
        if segments[i].0 < minLeft {
            minLeft := segments[i].0;
        }
        if segments[i].1 > maxRight {
            maxRight := segments[i].1;
        }
        i := i + 1;
    }
    
    assert minLeft == MinLeft(segments);
    assert maxRight == MaxRight(segments);
    
    i := 0;
    while i < n
        invariant 0 <= i <= n
        invariant forall j :: 0 <= j < i ==> 
            !(segments[j].0 == minLeft && segments[j].1 == maxRight)
    {
        if segments[i].0 == minLeft && segments[i].1 == maxRight {
            // Found a segment with min left and max right
            forall j | 0 <= j < n
            ensures segments[i].0 <= segments[j].0
            {
                MinLeftProperty(segments, j);
            }
            forall j | 0 <= j < n  
            ensures segments[i].1 >= segments[j].1
            {
                MaxRightProperty(segments, j);
            }
            assert HasMinLeftAndMaxRight(segments, i);
            HasMinLeftAndMaxRightImpliesCoversAll(segments, i);
            result := i + 1;
            return;
        }
        i := i + 1;
    }
    
    result := -1;
}
// </vc-code>

