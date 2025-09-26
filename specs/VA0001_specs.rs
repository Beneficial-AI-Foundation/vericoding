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
fn solve(n: i8, pos: i8, l: i8, r: i8) -> (result: i8)
    requires 
        valid_input(n as int, pos as int, l as int, r as int)
    ensures 
        result as int >= 0,
        no_tabs_to_close(l as int, r as int, n as int) ==> result as int == 0,
        only_close_right(l as int, r as int, n as int) ==> result as int == if pos as int >= r as int { pos as int - r as int } else { r as int - pos as int } + 1,
        only_close_left(l as int, r as int, n as int) ==> result as int == if pos as int >= l as int { pos as int - l as int } else { l as int - pos as int } + 1,
        close_both_sides(l as int, r as int, n as int) && l as int <= pos as int && pos as int <= r as int && (pos as int - l as int) < (r as int - pos as int) ==> result as int == (pos as int - l as int) + 1 + (r as int - l as int) + 1,
        close_both_sides(l as int, r as int, n as int) && l as int <= pos as int && pos as int <= r as int && (pos as int - l as int) >= (r as int - pos as int) ==> result as int == (r as int - pos as int) + 1 + (r as int - l as int) + 1,
        close_both_sides(l as int, r as int, n as int) && pos as int > r as int ==> result as int == (pos as int - r as int) + 1 + (r as int - l as int) + 1,
        close_both_sides(l as int, r as int, n as int) && pos as int < l as int ==> result as int == (l as int - pos as int) + 1 + (r as int - l as int) + 1,
        result as int <= 2 * n as int
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>


}

fn main() {}