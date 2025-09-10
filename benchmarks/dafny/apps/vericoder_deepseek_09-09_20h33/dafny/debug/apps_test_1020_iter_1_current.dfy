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
lemma PerimeterLemma(w: int, h: int, k: int)
    requires w >= 3 && h >= 3 && k >= 0
    requires w - 4 * k >= 3 && h - 4 * k >= 3
    ensures computeSum(w, h, k) == if k > 0 then perimeter(w, h) + computeSum(w - 4, h - 4, k - 1) else 0
{
    if k != 0 {
        // Dafny can prove the recursive case from the function definition
    }
}

lemma PerimeterFormula(w: int, h: int)
    requires w >= 1 && h >= 1
    ensures perimeter(w, h) == 2 * w + 2 * h - 4
{
}
// </vc-helpers>

// <vc-spec>
method GildCells(w: int, h: int, k: int) returns (result: int)
    requires ValidInput(w, h, k)
    ensures result == computeSum(w, h, k)
// </vc-spec>
// <vc-code>
{
    if k == 0 {
        result := 0;
    } else {
        var inner := GildCells(w - 4, h - 4, k - 1);
        PerimeterLemma(w, h, k);
        PerimeterFormula(w, h);
        result := 2 * w + 2 * h - 4 + inner;
    }
}
// </vc-code>

