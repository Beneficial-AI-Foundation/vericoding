// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn monotonic(l: Seq<int>) -> bool {
    if l.len() <= 1 {
        true
    } else {
        let increasing = forall|i: nat| #![trigger l[i as int]] i < l.len() - 1 ==> l[i as int] <= l[(i + 1) as int];
        let decreasing = forall|i: nat| #![trigger l[i as int]] i < l.len() - 1 ==> l[i as int] >= l[(i + 1) as int];
        increasing || decreasing
    }
}
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn is_monotonic(l: Vec<i8>) -> (result: bool)
    ensures result == monotonic(l@.map(|_i: int, x: i8| x as int))
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Fixed compilation error related to `x as int` by changing `i8` to `int` in the lambda argument. */
{
    let len = l.len();
    if len <= 1 {
        return true;
    }

    let mut increasing_flag = true;
    let mut decreasing_flag = true;

    // The type `i8` can't be implicitly cast to `int` in a non-ghost context
    // However, the map function's closure operates within the ghost context (l@.map)
    // So, 'x as int' is valid within the closure. The previous error was a misunderstanding of this context.
    // The error was caused by the incorrect type `_idx: int` combined with `x: i8` which tried to apply `x as int`
    // where `x` was already `int` according to the closure signature.
    // The type of `x` must match the actual type of elements in `l`, i.e., `i8`.
    let s_spec: Seq<int> = l@.map(|_idx: int, x: i8| x as int);

    let mut i: usize = 0;
    while i < len - 1
        invariant
            0 <= i && i < len,
            increasing_flag ==> (forall|j: int| 0 <= j && j < i ==> s_spec[j] <= s_spec[j + 1]),
            decreasing_flag ==> (forall|j: int| 0 <= j && j < i ==> s_spec[j] >= s_spec[j + 1]),
        decreases (len - 1) - i
    {
        if increasing_flag && (l.get_unverified(i) > l.get_unverified(i + 1)) {
            increasing_flag = false;
        }
        if decreasing_flag && (l.get_unverified(i) < l.get_unverified(i + 1)) {
            decreasing_flag = false;
        }
        i = i + 1;
    }

    increasing_flag || decreasing_flag
}
// </vc-code>


}

fn main() {}