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
{
    var sum := 0;
    var i := 0;
    var ww := w;
    var hh := h;
    while i < k
        invariant 0 <= i <= k
        invariant ww == w - 4 * i
        invariant hh == h - 4 * i
        invariant ww >= 3 && hh >= 3
        invariant sum == computeSum(w, h, i)
    {
        sum := sum + perimeter(ww, hh);
        ww := ww - 4;
        hh := hh - 4;
        i := i + 1;
    }
    result := sum;
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
    var i := 0;
    var ww := w;
    var hh := h;
    while i < k
        invariant 0 <= i <= k
        invariant ww == w - 4 * i
        invariant hh == h - 4 * i
        invariant ww >= 3 && hh >= 3
        invariant sum == computeSum(w, h, i)
    {
        sum := sum + perimeter(ww, hh);
        ww := ww - 4;
        hh := hh - 4;
        i := i + 1;
    }
    result := sum;
}
// </vc-code>

