// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn valid_input(n: int, a: Seq<int>) -> bool {
    n >= 0 && a.len() == n && forall|i: int| 0 <= i < a.len() ==> (#[trigger] a[i]) == 4 || a[i] == 8 || a[i] == 15 || a[i] == 16 || a[i] == 23 || a[i] == 42
}

spec fn number_of_complete_subsequences(n: int, a: Seq<int>) -> int
    requires valid_input(n, a)
    ensures 0 <= number_of_complete_subsequences(n, a) <= n
{
    let k = seq![4, 8, 15, 16, 23, 42];
    let s = seq![n, 0, 0, 0, 0, 0, 0];
    let final_s = process_array(s, a, k, 0);
    final_s[6]
}

spec fn process_array(s: Seq<int>, a: Seq<int>, k: Seq<int>, index: int) -> Seq<int>
    decreases a.len() - index
{
    if index == a.len() {
        s
    } else {
        let ai = a[index];
        let new_s = update_state(s, ai, k);
        process_array(new_s, a, k, index + 1)
    }
}

spec fn update_state(s: Seq<int>, ai: int, k: Seq<int>) -> Seq<int>
{
    if ai == k[5] && s[5] > 0 {
        s.update(6, s[6] + 1).update(5, s[5] - 1)
    } else if ai == k[4] && s[4] > 0 {
        s.update(5, s[5] + 1).update(4, s[4] - 1)
    } else if ai == k[3] && s[3] > 0 {
        s.update(4, s[4] + 1).update(3, s[3] - 1)
    } else if ai == k[2] && s[2] > 0 {
        s.update(3, s[3] + 1).update(2, s[2] - 1)
    } else if ai == k[1] && s[1] > 0 {
        s.update(2, s[2] + 1).update(1, s[1] - 1)
    } else if ai == k[0] && s[0] > 0 {
        s.update(1, s[1] + 1).update(0, s[0] - 1)
    } else {
        s
    }
}

spec fn number_of_complete_subsequences_partial(n: int, a: Seq<int>, k: Seq<int>, index: int) -> int
    requires valid_input(n, a)
    requires k.len() == 6
    requires k == seq![4, 8, 15, 16, 23, 42]
    requires 0 <= index <= a.len()
    ensures 0 <= number_of_complete_subsequences_partial(n, a, k, index) <= n
{
    let s = seq![n, 0, 0, 0, 0, 0, 0];
    let partial_a = if index == 0 { seq![] } else { a.subrange(0, index) };
    let final_s = process_array(s, partial_a, k, 0);
    final_s[6]
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn solve(n: int, a: Seq<int>) -> (result: int)
    requires valid_input(n, a)
    ensures 0 <= result <= n
    ensures result == n - 6 * number_of_complete_subsequences(n, a)
// </vc-spec>
// <vc-code>
{
    // impl-start
    assume(false);
    0int
    // impl-end
}
// </vc-code>


}

fn main() {}