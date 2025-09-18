// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn count_occurrences(a: Seq<i32>, key: i32) -> nat {
    a.filter(|x: i32| x == key).len()
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Fixed return type from usize to nat */
proof fn count_occurrences_extend(a: Seq<i32>, i: int, key: i32, old_count: nat)
    requires
        0 <= i < a.len(),
        old_count == count_occurrences(a.subrange(0, i), key),
    ensures
        count_occurrences(a.subrange(0, i + 1), key) == if a[i] == key { old_count + 1 } else { old_count },
{
    assert(a.subrange(0, i + 1) =~= a.subrange(0, i).push(a[i]));
}
// </vc-helpers>

// <vc-spec>
fn only_once(a: &Vec<i32>, key: i32) -> (result: bool)
    ensures
        result <==> count_occurrences(a@, key) == 1,
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Changed count type from usize to nat for type consistency */
    let mut count: nat = 0;
    let mut i: usize = 0;
    while i < a.len()
        invariant
            0 <= i <= a.len(),
            count == count_occurrences(a@.subrange(0, i as int), key),
        decreases a.len() - i,
    {
        let old_count = count;
        if a[i] == key {
            count = count + 1;
        }
        proof {
            count_occurrences_extend(a@, i as int, key, old_count);
        }
        i = i + 1;
    }
    assert(a@.subrange(0, a.len() as int) =~= a@);
    count == 1
}
// </vc-code>

}
fn main() {}