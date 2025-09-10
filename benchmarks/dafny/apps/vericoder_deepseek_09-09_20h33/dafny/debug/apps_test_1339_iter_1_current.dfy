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
lemma MinLeftLemma(segments: seq<(int, int)>, i: int)
    requires |segments| > 0
    requires 0 <= i < |segments|
    ensures MinLeft(segments) <= segments[i].0
{
    if |segments| == 1 {
    } else {
        if i == 0 {
        } else {
            MinLeftLemma(segments[1..], i-1);
        }
    }
}

lemma MaxRightLemma(segments: seq<(int, int)>, i: int)
    requires |segments| > 0
    requires 0 <= i < |segments|
    ensures MaxRight(segments) >= segments[i].1
{
    if |segments| == 1 {
    } else {
        if i == 0 {
        } else {
            MaxRightLemma(segments[1..], i-1);
        }
    }
}

lemma MinLeftExists(segments: seq<(int, int)>)
    requires |segments| > 0
    ensures exists i :: 0 <= i < |segments| && segments[i].0 == MinLeft(segments)
{
    if |segments| == 1 {
    } else {
        if segments[0].0 <= MinLeft(segments[1..]) {
        } else {
            MinLeftExists(segments[1..]);
        }
    }
}

lemma MaxRightExists(segments: seq<(int, int)>)
    requires |segments| > 0
    ensures exists i :: 0 <= i < |segments| && segments[i].1 == MaxRight(segments)
{
    if |segments| == 1 {
    } else {
        if segments[0].1 >= MaxRight(segments[1..]) {
        } else {
            MaxRightExists(segments[1..]);
        }
    }
}

lemma HasMinLeftAndMaxRightImpliesCoversAll(segments: seq<(int, int)>, idx: int)
    requires 0 <= idx < |segments|
    requires HasMinLeftAndMaxRight(segments, idx)
    ensures CoversAll(segments, idx)
{
    MinLeftLemma(segments, idx);
    MaxRightLemma(segments, idx);
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
    
    var candidate := -1;
    var i := 0;
    while i < n
        invariant 0 <= i <= n
        invariant candidate == -1 || (0 <= candidate < n && HasMinLeftAndMaxRight(segments, candidate))
        invariant candidate == -1 ==> forall j :: 0 <= j < i ==> !HasMinLeftAndMaxRight(segments, j)
    {
        if segments[i].0 == minLeft && segments[i].1 == maxRight {
            candidate := i;
            break;
        }
        i := i + 1;
    }
    
    if candidate != -1 {
        result := candidate + 1;
    } else {
        result := -1;
    }
}
// </vc-code>

