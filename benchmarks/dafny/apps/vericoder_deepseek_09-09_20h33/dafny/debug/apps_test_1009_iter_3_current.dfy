predicate ValidInput(n: int, k: int, L: seq<int>)
{
    n >= 1 && k >= 1 && n <= 2*k &&
    |L| == n &&
    (forall i :: 0 <= i < |L|-1 ==> L[i] <= L[i+1]) &&
    (forall i :: 0 <= i < |L| ==> L[i] >= 0)
}

predicate ValidBoxConfiguration(boxes: seq<int>, boxSize: int)
{
    |boxes| >= 1 &&
    (forall i :: 0 <= i < |boxes| ==> boxes[i] <= boxSize) &&
    (forall i :: 0 <= i < |boxes| ==> boxes[i] >= 0)
}

function sum(s: seq<int>): int
{
    if |s| == 0 then 0 else s[0] + sum(s[1..])
}

function max(s: seq<int>): int
    requires |s| > 0
{
    if |s| == 1 then s[0]
    else if s[0] >= max(s[1..]) then s[0]
    else max(s[1..])
}

// <vc-helpers>
lemma LemmaSumNonNegative(s: seq<int>)
    ensures sum(s) >= 0
{
    if |s| > 0 {
        LemmaSumNonNegative(s[1..]);
        // sum(s) = s[0] + sum(s[1..]) >= s[0] >= 0
    }
}

lemma LemmaMaxGreaterEqual(s: seq<int>, i: int)
    requires |s| > 0 && 0 <= i < |s|
    ensures max(s) >= s[i]
{
    if |s| == 1 {
        // trivial
    } else {
        if i == 0 {
            if s[0] >= max(s[1..]) {
                // s[0] is max
            } else {
                LemmaMaxGreaterEqual(s[1..], 0);
                assert max(s[1..]) >= s[0];
            }
        } else {
            LemmaMaxGreaterEqual(s[1..], i-1);
            if s[0] >= max(s[1..]) {
                assert max(s) == s[0];
                assert s[0] >= s[1..][i-1] by { LemmaMaxGreaterEqual(s[1..], i-1); }
                assert s[1..][i-1] == s[i];
            } else {
                assert max(s) == max(s[1..]);
                assert max(s[1..]) >= s[1..][i-1] by { LemmaMaxGreaterEqual(s[1..], i-1); }
                assert s[1..][i-1] == s[i];
            }
        }
    }
}

lemma LemmaMaxAtLeastSumOverLength(s: seq<int>)
    requires |s| > 0
    ensures max(s) * |s| >= sum(s)
{
    if |s| == 1 {
        // trivial: max(s) * 1 = s[0] = sum(s)
    } else {
        LemmaMaxAtLeastSumOverLength(s[1..]);
        var m := max(s);
        if s[0] >= max(s[1..]) {
            assert m == s[0];
            assert m * |s| == s[0] + m * (|s| - 1);
            assert m * (|s| - 1) >= sum(s[1..]) by { LemmaMaxAtLeastSumOverLength(s[1..]); }
        } else {
            assert m == max(s[1..]);
            assert m * |s| == m + m * (|s| - 1);
            assert m * (|s| - 1) >= sum(s[1..]) by { LemmaMaxAtLeastSumOverLength(s[1..]); }
            assert m >= s[0] by { LemmaMaxGreaterEqual(s[1..], 0); }
        }
    }
}

predicate CanPack(L: seq<int>, boxSize: int, k: int)
    requires ValidInput(|L|, k, L)
    requires boxSize >= 0
{
    if boxSize == 0 then
        sum(L) == 0
    else
        boxSize >= max(L) && boxSize * k >= sum(L)
}
// </vc-helpers>

// <vc-spec>
method solve(n: int, k: int, L: seq<int>) returns (result: int)
    requires ValidInput(n, k, L)
    ensures result >= 0
// </vc-spec>
// <vc-code>
{
    var low := 0;
    var high := sum(L);
    // Initialize loop invariants properly
    assert high >= 0 by { LemmaSumNonNegative(L); }
    
    while low <= high
        invariant 0 <= low <= high + 1
        invariant high >= 0
        invariant low >= 0
    {
        var mid := (low + high) / 2;
        if mid < 0 {
            mid := 0;
        }
        if CanPack(L, mid, k) {
            high := mid - 1;
            if high < 0 {
                high := 0;
            }
        } else {
            low := mid + 1;
        }
    }
    
    result := low;
    assert result >= 0;
}
// </vc-code>

