predicate ValidInput(n: int, pos: int, l: int, r: int)
{
    1 <= n <= 100 && 1 <= pos <= n && 1 <= l <= r <= n
}

predicate NoTabsToClose(l: int, r: int, n: int)
{
    l == 1 && r == n
}

predicate OnlyCloseRight(l: int, r: int, n: int)
{
    l == 1 && r < n
}

predicate OnlyCloseLeft(l: int, r: int, n: int)
{
    l > 1 && r == n
}

predicate CloseBothSides(l: int, r: int, n: int)
{
    l > 1 && r < n
}

// <vc-helpers>
function abs(x: int): int
{
    if x >= 0 then x else -x
}
// </vc-helpers>

// <vc-spec>
method solve(n: int, pos: int, l: int, r: int) returns (result: int)
    requires ValidInput(n, pos, l, r)
    ensures result >= 0
    ensures NoTabsToClose(l, r, n) ==> result == 0
    ensures OnlyCloseRight(l, r, n) ==> result == abs(pos - r) + 1
    ensures OnlyCloseLeft(l, r, n) ==> result == abs(pos - l) + 1
    ensures CloseBothSides(l, r, n) && l <= pos <= r && pos - l < r - pos ==> result == (pos - l) + 1 + (r - l) + 1
    ensures CloseBothSides(l, r, n) && l <= pos <= r && pos - l >= r - pos ==> result == (r - pos) + 1 + (r - l) + 1
    ensures CloseBothSides(l, r, n) && pos > r ==> result == (pos - r) + 1 + (r - l) + 1
    ensures CloseBothSides(l, r, n) && pos < l ==> result == (l - pos) + 1 + (r - l) + 1
    ensures result <= 2 * n
// </vc-spec>
// <vc-code>
{
    if l == 1 && r == n {
        result := 0;
    } else if l == 1 && r < n {
        result := abs(pos - r) + 1;
    } else if l > 1 && r == n {
        result := abs(pos - l) + 1;
    } else {
        // l > 1 && r < n (CloseBothSides)
        if pos < l {
            result := (l - pos) + 1 + (r - l) + 1;
        } else if pos > r {
            result := (pos - r) + 1 + (r - l) + 1;
        } else {
            // l <= pos <= r
            if pos - l < r - pos {
                result := (pos - l) + 1 + (r - l) + 1;
            } else {
                result := (r - pos) + 1 + (r - l) + 1;
            }
        }
    }
}
// </vc-code>

