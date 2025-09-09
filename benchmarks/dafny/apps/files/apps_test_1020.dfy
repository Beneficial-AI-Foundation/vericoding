Given a rectangular plate with dimensions w × h cells, calculate the total number of cells
to be gilded when adding k concentric rings. Ring 1 is the border of the full w × h rectangle,
Ring 2 is the border of the inner (w-4) × (h-4) rectangle, and so on. Each ring consists of
all cells on the perimeter of its respective rectangle.

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

lemma ComputeSumLemma(w: int, h: int, i: int)
    requires w >= 3 && h >= 3 && i >= 0
    requires w - 4 * (i + 1) >= 3 && h - 4 * (i + 1) >= 3
    ensures computeSum(w, h, i + 1) == computeSum(w, h, i) + perimeter(w - 4 * i, h - 4 * i)
{
    if i == 0 {
        assert computeSum(w, h, 1) == perimeter(w, h) + computeSum(w - 4, h - 4, 0);
        assert computeSum(w - 4, h - 4, 0) == 0;
        assert computeSum(w, h, 0) == 0;
        assert perimeter(w - 4 * 0, h - 4 * 0) == perimeter(w, h);
    } else {
        assert computeSum(w, h, i + 1) == perimeter(w, h) + computeSum(w - 4, h - 4, i);
        ComputeSumLemma(w - 4, h - 4, i - 1);
        assert computeSum(w - 4, h - 4, i) == computeSum(w - 4, h - 4, i - 1) + perimeter((w - 4) - 4 * (i - 1), (h - 4) - 4 * (i - 1));
        assert (w - 4) - 4 * (i - 1) == w - 4 * i;
        assert (h - 4) - 4 * (i - 1) == h - 4 * i;
        assert computeSum(w, h, i) == perimeter(w, h) + computeSum(w - 4, h - 4, i - 1);
    }
}

method GildCells(w: int, h: int, k: int) returns (result: int)
    requires ValidInput(w, h, k)
    ensures result == computeSum(w, h, k)
{
    var ans := 0;
    var curr_w := w;
    var curr_h := h;
    var i := 0;

    while i < k
        invariant 0 <= i <= k
        invariant curr_w == w - 4 * i
        invariant curr_h == h - 4 * i
        invariant curr_w >= 3 && curr_h >= 3
        invariant ans == computeSum(w, h, i)
        invariant w - 4 * i >= 3 && h - 4 * i >= 3
        invariant w - 4 * k >= 3 && h - 4 * k >= 3
    {
        ans := ans + curr_w * 2 + (curr_h - 2) * 2;
        curr_w := curr_w - 4;
        curr_h := curr_h - 4;
        i := i + 1;

        ComputeSumLemma(w, h, i - 1);
    }

    result := ans;
}
