// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): added bounds checking helper to ensure cast safety */
spec fn valid_index_for_cast(index: usize, len: usize) -> bool {
    index < len && index <= 0x7fff_ffff
}

spec fn contains_at(a: &Vec<i32>, key: i32, index: int) -> bool {
    0 <= index < a.len() && a[index] == key
}

spec fn not_found_before(a: &Vec<i32>, key: i32, index: int) -> bool {
    forall|i: int| 0 <= i < index ==> a[i] != key
}

spec fn not_found_anywhere(a: &Vec<i32>, key: i32) -> bool {
    forall|i: int| 0 <= i < a.len() ==> a[i] != key
}
// </vc-helpers>

// <vc-spec>
fn find(a: &Vec<i32>, key: i32) -> (result: i32)
    ensures
        (result == -1 || (result >= 0 && result < a.len())),
        result != -1 ==> (a[result as int] == key && forall|i: int| 0 <= i < result ==> a[i] != key),
        result == -1 ==> forall|i: int| 0 <= i < a.len() ==> a[i] != key,
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): fixed assertion syntax with proper operator grouping */
    let mut i: usize = 0;
    while i < a.len()
        invariant
            i <= a.len(),
            forall|j: int| 0 <= j < i ==> a[j] != key,
        decreases a.len() - i
    {
        if a[i] == key {
            proof {
                assert(i < a.len());
                assert(i <= 0x7fff_ffff);
                assert(0 <= i as int && (i as int) < a.len());
            }
            return i as i32;
        }
        i += 1;
    }
    -1
}
// </vc-code>

}
fn main() {}