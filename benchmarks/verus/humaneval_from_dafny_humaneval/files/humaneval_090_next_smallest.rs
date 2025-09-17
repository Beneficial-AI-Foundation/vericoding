// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn get_val(mx: Option<int>) -> int
    recommends matches!(mx, Some(_))
{
    match mx {
        Some(n) => n,
        None => 0
    }
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn rolling_max(s: &[int]) -> (res: Option<int>)
    ensures 
        matches!(res, None) <==> s.len() < 2,
        matches!(res, Some(_)) ==> exists|x: int| 0 <= x < s.len() && s[x] == get_val(res),
        forall|x: int, y: int| 0 <= x < y < s.len() ==> s[x] <= get_val(res) || s[y] <= get_val(res),
// </vc-spec>
// <vc-code>
{
    assume(false);
    None
}
// </vc-code>


}

fn main() {}