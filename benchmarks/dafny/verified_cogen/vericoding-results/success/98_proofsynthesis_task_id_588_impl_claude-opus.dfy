// <vc-preamble>
function MaxRcur(s: seq<int>): int
    requires |s| > 0
    decreases |s|
{
    if |s| <= 1 then
        s[0]
    else
        var last := s[|s|-1];
        var rest := MaxRcur(s[..|s|-1]);
        if last > rest then last else rest
}

function MinRcur(s: seq<int>): int
    requires |s| > 0
    decreases |s|
{
    if |s| <= 1 then
        s[0]
    else
        var last := s[|s|-1];
        var rest := MinRcur(s[..|s|-1]);
        if last < rest then last else rest
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): Added lemmas to prove loop maintains max/min invariants */
function Max(a: int, b: int): int { if a > b then a else b }

function Min(a: int, b: int): int { if a < b then a else b }

lemma MaxRcurExtend(s: seq<int>, x: int)
    requires |s| > 0
    ensures MaxRcur(s + [x]) == Max(MaxRcur(s), x)
{
    if |s| == 1 {
        assert s + [x] == [s[0], x];
        assert MaxRcur(s + [x]) == Max(s[0], x);
        assert MaxRcur(s) == s[0];
    } else {
        var init := s[..|s|-1];
        var last := s[|s|-1];
        assert s == init + [last];
        assert s + [x] == init + [last, x];
        assert MaxRcur(s + [x]) == Max(x, Max(last, MaxRcur(init)));
        assert MaxRcur(s) == Max(last, MaxRcur(init));
        assert Max(MaxRcur(s), x) == Max(Max(last, MaxRcur(init)), x);
        assert Max(Max(last, MaxRcur(init)), x) == Max(x, Max(last, MaxRcur(init)));
    }
}

lemma MinRcurExtend(s: seq<int>, x: int)
    requires |s| > 0
    ensures MinRcur(s + [x]) == Min(MinRcur(s), x)
{
    if |s| == 1 {
        assert s + [x] == [s[0], x];
        assert MinRcur(s + [x]) == Min(s[0], x);
        assert MinRcur(s) == s[0];
    } else {
        var init := s[..|s|-1];
        var last := s[|s|-1];
        assert s == init + [last];
        assert s + [x] == init + [last, x];
        assert MinRcur(s + [x]) == Min(x, Min(last, MinRcur(init)));
        assert MinRcur(s) == Min(last, MinRcur(init));
        assert Min(MinRcur(s), x) == Min(Min(last, MinRcur(init)), x);
        assert Min(Min(last, MinRcur(init)), x) == Min(x, Min(last, MinRcur(init)));
    }
}
// </vc-helpers>

// <vc-spec>
method DifferenceMaxMin(arr: array<int>) returns (diff: int)
    requires arr.Length > 0
    requires forall i :: 0 <= i < arr.Length ==> -1073741824 < arr[i] < 1073741823
    ensures diff == MaxRcur(arr[..]) - MinRcur(arr[..])
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 2): Fixed loop invariants using helper lemmas */
{
    var maxVal := arr[0];
    var minVal := arr[0];
    var i := 1;
    
    while i < arr.Length
        invariant 1 <= i <= arr.Length
        invariant maxVal == MaxRcur(arr[..i])
        invariant minVal == MinRcur(arr[..i])
    {
        assert arr[..i+1] == arr[..i] + [arr[i]];
        MaxRcurExtend(arr[..i], arr[i]);
        MinRcurExtend(arr[..i], arr[i]);
        
        maxVal := Max(maxVal, arr[i]);
        minVal := Min(minVal, arr[i]);
        i := i + 1;
    }
    
    assert arr[..i] == arr[..];
    diff := maxVal - minVal;
}
// </vc-code>
