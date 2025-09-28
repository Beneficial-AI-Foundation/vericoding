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
/* helper modified by LLM (iteration 4): Removed unnecessary helper; `max` is built-in. */
// </vc-helpers>

// <vc-spec>
fn rolling_max(s: &Vec<i8>) -> (res: Option<i8>)
    ensures 
        matches!(res, None) <==> s@.len() < 2,
        matches!(res, Some(_)) ==> exists|x: int| 0 <= x < s@.len() && s@[x] as int == get_val(match res { Some(v) => Some(v as int), None => None }),
        forall|x: int, y: int| 0 <= x < y < s@.len() ==> s@[x] as int <= get_val(match res { Some(v) => Some(v as int), None => None }) || s@[y] as int <= get_val(match res { Some(v) => Some(v as int), None => None }),
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 4): The problem was that the invariant `0 <= k < i && s@.index(k) == current_max` was not strong enough. It only guaranteed that `current_max` appeared in the prefix. The `current_max` must be the *maximum* value in the prefix `s[0..i]`. The issue was fixed by changing the invariant to explicitly state that all elements `s.index(j)` where `j` is in `0..i` must be less than or equal to `current_max`. */
{
    if s.len() < 2 {
        return None;
    }

    let mut current_max: i8 = s[0];
    let mut i: usize = 1;

    while i < s.len()
        invariant 
            1 <= i && i <= s.len(),
            exists|k: int| 0 <= k < i && s@.index(k) as int == current_max as int,
            forall|j: int| 0 <= j < i ==> s@.index(j) as int <= current_max as int
        decreases s.len() - i
    {
        if s[i] > current_max {
            current_max = s[i];
        }
        i = i + 1;
    }

    Some(current_max)
}
// </vc-code>


}

fn main() {}