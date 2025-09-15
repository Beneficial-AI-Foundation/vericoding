// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Fixed seq_index_of parameter type and added proper lemma */
proof fn lemma_seq_len_nonnegative<T>(s: Seq<T>)
    ensures
        s.len() >= 0,
{
}

spec fn seq_index_of<T>(s: Seq<T>, key: T) -> int {
    s.index_of(|x| x == key)
}

spec fn bounded_int_to_nat(i: int, bound: int) -> nat
    requires
        i >= 0,
        i < bound,
{
    i as nat
}

proof fn lemma_usize_to_int_conversion(n: usize) -> (result: int)
    ensures result == n as int
{
    n as int
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
/* code modified by LLM (iteration 5): Fixed integer index handling with proper usize conversion */
{
    let mut index: i32 = 0;
    let len = a.len() as i32;
    
    while index < len
        invariant
            0 <= index <= len,
            forall|i: int| 0 <= i < index as int ==> a[i] != key,
        decreases (len - index),
    {
        let idx_usize: usize = index as usize;
        if a[idx_usize] == key {
            return index;
        }
        index = index + 1;
    }
    
    -1
}
// </vc-code>

}
fn main() {}