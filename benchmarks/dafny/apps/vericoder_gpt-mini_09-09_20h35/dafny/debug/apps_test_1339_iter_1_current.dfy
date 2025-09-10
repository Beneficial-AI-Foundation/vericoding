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
        // MinLeft(segments) == segments[0].0, trivially <= segments[0].0
    } else {
        var rest := segments[1..];
        MinLeft_le_all(rest);
        var mrest := MinLeft(rest);
        if segments[0].0 <= mrest {
            // MinLeft(segments) == segments[0].0
            // For j == 0 holds; for j > 0: segments[0].0 <= mrest <= segments[j].0
            // Use IH: mrest <= segments[j].0 for j>0
            assert MinLeft(segments) == segments[0].0;
            forall j | 0 <= j < |segments| {
                if j == 0 {
                    assert MinLeft(segments) <= segments[j].0;
                } else {
                    // j-1 is in rest
                    assert MinLeft(segments) == segments[0].0;
                    assert segments[0].0 <= mrest;
                    // from IH: mrest <= segments[j].0
                    assert mrest <= segments[j].0;
                    assert MinLeft(segments) <= segments[j].0;
                }
            }
        } else {
            // segments[0].0 > mrest, so MinLeft(segments) == mrest
            assert MinLeft(segments) == mrest;
            forall j | 0 <= j < |segments| {
                if j == 0 {
                    // segments[0].0 >= mrest
                    assert MinLeft(segments) <= segments[j].0;
                } else {
                    // j-1 in rest and IH gives mrest <= rest[j-1].0 == segments[j].0
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
        // MaxRight(segments) == segments[0].1
    } else {
        var rest := segments[1..];
        MaxRight_ge_all(rest);
        var rrest := MaxRight(rest);
        if segments[0].1 >= rrest {
            // MaxRight(segments) == segments[0].1
            assert MaxRight(segments) == segments[0].1;
            forall j | 0 <= j < |segments| {
                if j == 0 {
                    assert MaxRight(segments) >= segments[j].1;
                } else {
                    // from IH rrest >= segments[j].1
                    assert rrest >= segments[j].1;
                    assert segments[0].1 >= rrest;
                    assert MaxRight(segments) >= segments[j].1;
                }
            }
        } else {
            // MaxRight(segments) == rrest
            assert MaxRight(segments) == rrest;
            forall j | 0 <= j < |segments| {
                if j == 0 {
                    // segments[0].1 <= rrest
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

