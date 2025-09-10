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

// </vc-helpers>

// <vc-spec>
method GildCells(w: int, h: int, k: int) returns (result: int)
    requires ValidInput(w, h, k)
    ensures result == computeSum(w, h, k)
// </vc-spec>
// <vc-code>
{
  result := 0;
  var current_w := w;
  var current_h := h;
  var i := k;
  while i > 0
    invariant 0 <= i <= k
    invariant current_w == w - 4 * (k - i)
    invariant current_h == h - 4 * (k - i)
    invariant result + computeSum(current_w, current_h, i) == computeSum(w, h, k)
  {
    result := result + perimeter(current_w, current_h);
    current_w := current_w - 4;
    current_h := current_h - 4;
    i := i - 1;
  }
}
// </vc-code>

