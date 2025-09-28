// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn count_occurrences(a: Seq<i32>, key: i32) -> nat {
    a.filter(|x: i32| x == key).len()
}
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn only_once(a: &Vec<i32>, key: i32) -> (result: bool)
    ensures
        result <==> count_occurrences(a@, key) == 1,
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): The compilation error is `found_count == count_occurrences(a@.take(i as nat), key) as usize,` where `a@.take(i as nat)` is passed to `count_occurrences`. `count_occurrences` expects `Seq<i32>` for `a`, not `Seq<i32>` converted to `usize`. The issue is the `as usize` cast. The `count_occurrences` returns `nat`, which is an `int` in Verus. We are comparing it to `found_count` of type `usize`. We should explicitly convert the `found_occurrences` to `nat` for the comparison with `count_occurrences`'s return type */
{
    let mut found_count: usize = 0;
    let mut i: usize = 0;

    while i < a.len()
        invariant 
            0 <= i && i <= a.len(),
            found_count as nat == count_occurrences(a@.take(i as nat), key),
            found_count <= 1,
        decreases a.len() - i
    {
        if a[i] == key {
            found_count = found_count + 1;
        }
        i = i + 1;
    }
    found_count == 1
}
// </vc-code>

}
fn main() {}