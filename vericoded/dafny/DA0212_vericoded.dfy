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
lemma ComputeSumUnroll(w: int, h: int, k: int, acc: int)
    requires w >= 3 && h >= 3 && k >= 0
    requires w - 4 * k >= 3 && h - 4 * k >= 3
    ensures acc + computeSum(w, h, k) == acc + (if k == 0 then 0 else perimeter(w, h) + computeSum(w - 4, h - 4, k - 1))
{
    // This lemma helps verify the loop invariant maintains the correct relationship
}
// </vc-helpers>

// <vc-spec>
method GildCells(w: int, h: int, k: int) returns (result: int)
    requires ValidInput(w, h, k)
    ensures result == computeSum(w, h, k)
// </vc-spec>
// <vc-code>
{
    var sum := 0;
    var currentW := w;
    var currentH := h;
    var remaining := k;
    
    while remaining > 0
        invariant 0 <= remaining <= k
        invariant currentW == w - 4 * (k - remaining)
        invariant currentH == h - 4 * (k - remaining)
        invariant currentW >= 3 && currentH >= 3
        invariant sum == computeSum(w, h, k) - computeSum(currentW, currentH, remaining)
    {
        sum := sum + perimeter(currentW, currentH);
        currentW := currentW - 4;
        currentH := currentH - 4;
        remaining := remaining - 1;
    }
    
    result := sum;
}
// </vc-code>

