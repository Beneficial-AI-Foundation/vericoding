predicate ValidInput(w: int, h: int, k: int)
{
    w >= 3 && h >= 3 && w <= 100 && h <= 100 && 
    k >= 1 && k <= ((if w <= h then w else h) + 1) / 4 &&
    w - 4 * k >= 3 && h - 4 * k >= 3
}

function perimeter(w: int, h: int): int
    requires w >= 1 && h >= 1
{
    w * 2 + (h - 2) * 2
}

function computeSum(w: int, h: int, k: int): int
    requires w >= 3 && h >= 3 && k >= 0
    requires w - 4 * k >= 3 && h - 4 * k >= 3
    decreases k
{
    if k == 0 then 0
    else 
        perimeter(w, h) + computeSum(w - 4, h - 4, k - 1)
}

// <vc-helpers>
lemma ComputeSumIterativeEquivalence(w: int, h: int, k: int)
    requires w >= 3 && h >= 3 && k >= 0
    requires w - 4 * k >= 3 && h - 4 * k >= 3
    ensures computeSum(w, h, k) == ComputeSumIterative(w, h, k, 0)
{
    ComputeSumIterativeCorrectness(w, h, k, 0);
}

function ComputeSumIterative(w: int, h: int, k: int, i: int): int
    requires w >= 3 && h >= 3 && k >= 0 && i >= 0
    requires w - 4 * k >= 3 && h - 4 * k >= 3
    decreases k - i
{
    if i >= k then 0
    else perimeter(w - 4 * i, h - 4 * i) + ComputeSumIterative(w, h, k, i + 1)
}

lemma ComputeSumIterativeCorrectness(w: int, h: int, k: int, i: int)
    requires w >= 3 && h >= 3 && k >= 0 && i >= 0
    requires w - 4 * k >= 3 && h - 4 * k >= 3
    ensures computeSum(w - 4 * i, h - 4 * i, k - i) == ComputeSumIterative(w, h, k, i)
    decreases k - i
{
    if i >= k {
        assert k - i <= 0;
        assert computeSum(w - 4 * i, h - 4 * i, k - i) == 0;
        assert ComputeSumIterative(w, h, k, i) == 0;
    } else {
        var w' := w - 4 * i;
        var h' := h - 4 * i;
        var k' := k - i;
        assert k' > 0;
        assert computeSum(w', h', k') == perimeter(w', h') + computeSum(w' - 4, h' - 4, k' - 1);
        assert w' - 4 == w - 4 * (i + 1);
        assert h' - 4 == h - 4 * (i + 1);
        assert k' - 1 == k - (i + 1);
        ComputeSumIterativeCorrectness(w, h, k, i + 1);
        assert computeSum(w' - 4, h' - 4, k' - 1) == ComputeSumIterative(w, h, k, i + 1);
        assert ComputeSumIterative(w, h, k, i) == perimeter(w', h') + ComputeSumIterative(w, h, k, i + 1);
    }
}
// </vc-helpers>

// <vc-spec>
method GildCells(w: int, h: int, k: int) returns (result: int)
    requires ValidInput(w, h, k)
    ensures result == computeSum(w, h, k)
// </vc-spec>
// <vc-code>
{
    result := 0;
    var i := 0;
    var currentW := w;
    var currentH := h;
    
    while i < k
        invariant 0 <= i <= k
        invariant currentW == w - 4 * i
        invariant currentH == h - 4 * i
        invariant currentW >= 3 && currentH >= 3
        invariant result == ComputeSumIterative(w, h, k, 0) - ComputeSumIterative(w, h, k, i)
        decreases k - i
    {
        var perim := perimeter(currentW, currentH);
        result := result + perim;
        i := i + 1;
        currentW := currentW - 4;
        currentH := currentH - 4;
    }
    
    ComputeSumIterativeEquivalence(w, h, k);
}
// </vc-code>

