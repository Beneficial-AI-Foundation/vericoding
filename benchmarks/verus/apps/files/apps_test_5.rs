// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn valid_input(n: int, pos: int, l: int, r: int) -> bool {
    1 <= n <= 100 && 1 <= pos <= n && 1 <= l <= r <= n
}

spec fn no_tabs_to_close(l: int, r: int, n: int) -> bool {
    l == 1 && r == n
}

spec fn only_close_right(l: int, r: int, n: int) -> bool {
    l == 1 && r < n
}

spec fn only_close_left(l: int, r: int, n: int) -> bool {
    l > 1 && r == n
}

spec fn close_both_sides(l: int, r: int, n: int) -> bool {
    l > 1 && r < n
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn solve(n: int, pos: int, l: int, r: int) -> (result: int)
    requires 
        valid_input(n, pos, l, r)
    ensures 
        result >= 0,
        no_tabs_to_close(l, r, n) ==> result == 0,
        only_close_right(l, r, n) ==> result == if pos >= r { pos - r } else { r - pos } + 1,
        only_close_left(l, r, n) ==> result == if pos >= l { pos - l } else { l - pos } + 1,
        close_both_sides(l, r, n) && l <= pos <= r && pos - l < r - pos ==> result == (pos - l) + 1 + (r - l) + 1,
        close_both_sides(l, r, n) && l <= pos <= r && pos - l >= r - pos ==> result == (r - pos) + 1 + (r - l) + 1,
        close_both_sides(l, r, n) && pos > r ==> result == (pos - r) + 1 + (r - l) + 1,
        close_both_sides(l, r, n) && pos < l ==> result == (l - pos) + 1 + (r - l) + 1,
        result <= 2 * n
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>


}

fn main() {}