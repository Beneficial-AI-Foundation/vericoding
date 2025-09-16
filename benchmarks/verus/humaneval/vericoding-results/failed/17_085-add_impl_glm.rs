// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn odd_or_zero(x: u32) -> (ret:u32) {
    if x % 2 == 0 {
        x
    } else {
        0
    }
}

spec fn add_odd_evens(lst: Seq<u32>) -> (ret:int)
    decreases lst.len(),
{
    if (lst.len() < 2) {
        0
    } else {
        odd_or_zero(lst[1]) + add_odd_evens(lst.skip(2))
    }
}
// </vc-preamble>

// <vc-helpers>
spec fn sequence_to_vec(seq: Seq<u32>) -> Vec<u32>
    decreases seq.len(),
{
    if seq.len() == 0 {
        Seq::empty().to_vec()
    } else {
        let mut vec = sequence_to_vec(seq.drop_last());
        vec.push(seq.last());
        vec
    }
}

/* helper modified by LLM (iteration 5): change Vec::new() to Seq::empty().to_vec() to fix exec mode compilation error */
proof fn lemma_add_odd_evens_recursive(lst: Seq<u32>, i: int)
    requires
        0 <= i <= lst.len(),
    ensures
        add_odd_evens(lst) == add_odd_evens(lst.subrange(0, i as int)) + add_odd_evens(lst.subrange(i as int, lst.len() as int)),
    decreases i,
{
    if i == 0 || i == lst.len() {
        // Base case: empty subrange on one side
    } else {
        lemma_add_odd_evens_recursive(lst, i - 1);
    }
}

proof fn lemma_add_odd_evens_eq(lst: Seq<u32>, lst2: Seq<u32>)
    requires
        lst.len() == lst2.len(),
        forall|i: int| 0 <= i < lst.len() ==> lst[i] == lst2[i],
    ensures
        add_odd_evens(lst) == add_odd_evens(lst2),
    decreases lst.len(),
{
    if lst.len() < 2 {
        // Base case
    } else {
        assert(lst[1] == lst2[1]);
        assert(lst.skip(2).len() == lst2.skip(2).len());
        assert forall|i: int| 0 <= i < lst.skip(2).len() implies lst.skip(2)[i] == lst2.skip(2)[i] by {
            assert(lst.skip(2)[i] == lst[i + 2]);
            assert(lst2.skip(2)[i] == lst2[i + 2]);
        };
        lemma_add_odd_evens_eq(lst.skip(2), lst2.skip(2));
    }
}
// </vc-helpers>

// <vc-spec>
fn add(lst: Vec<u32>) -> (sum: u64)

    requires
        0 < lst.len() < u32::MAX,

    ensures
        sum == add_odd_evens(lst@),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): fix loop invariants and execution logic */
    let mut sum: u64 = 0;
    let mut i: usize = 0;
    let n = lst@.len();

    while i < n
        invariant
            0 <= i <= n,
            sum == add_odd_evens(lst@.subrange(0, i as int)),
        decreases n - i,
    {
        if i + 1 < n {
            // Get the second element of the pair
            let second = lst[i + 1];
            if second % 2 == 0 {
                sum += second as u64;
            }
            // Move to next pair
            i += 2;
        } else {
            // Handle case at odd index with no pair
            i += 1;
        }
    }

    sum
}
// </vc-code>

}
fn main() {}