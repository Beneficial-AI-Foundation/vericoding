Given n browser tabs indexed 1 to n with cursor at position pos, find minimum time to close
all tabs except those in range [l, r]. Operations: move cursor (1 sec), close all tabs to
left of cursor (1 sec), close all tabs to right of cursor (1 sec).

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

function abs(x: int): int
{
    if x >= 0 then x else -x
}

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
{
    if l > 1 && r < n {
        // Need to close both left and right sides
        if l <= pos && pos <= r {
            // Cursor is in target range
            if pos - l < r - pos {
                // Closer to left edge: go left first
                result := (pos - l) + 1 + (r - l) + 1;
            } else {
                // Closer to right edge: go right first
                result := (r - pos) + 1 + (r - l) + 1;
            }
        } else if pos > r {
            // Cursor is right of target range
            result := (pos - r) + 1 + (r - l) + 1;
        } else {
            // Cursor is left of target range
            result := (l - pos) + 1 + (r - l) + 1;
        }
    } else if l == 1 && r < n {
        // Only need to close right side
        var tmpCall1 := abs(pos - r);
        result := tmpCall1 + 1;
    } else if l > 1 && r == n {
        // Only need to close left side
        var tmpCall2 := abs(pos - l);
        result := tmpCall2 + 1;
    } else {
        // No tabs need to be closed
        result := 0;
    }
}
