use vstd::prelude::*;

verus! {

spec fn odd_or_zero(x: u32) -> (ret:u32) {
    if x % 2 == 0 {
        x
    } else {
        0
    }
}
// pure-end
// pure-end

spec fn add_odd_evens(lst: Seq<u32>) -> (ret:int)
    decreases lst.len(),
{
    if (lst.len() < 2) {
        0
    } else {
        odd_or_zero(lst[1]) + add_odd_evens(lst.skip(2))
    }
}
// pure-end

// <vc-helpers>
proof fn lemma_add_odd_evens_bounds(lst: Seq<u32>)
    requires
        lst.len() < u32::MAX,
    ensures
        0 <= add_odd_evens(lst) <= (lst.len() as int / 2 + 1) * (u32::MAX as int),
    decreases lst.len(),
{
    if lst.len() < 2 {
        assert(add_odd_evens(lst) == 0);
    } else {
        lemma_add_odd_evens_bounds(lst.skip(2));
        let val = odd_or_zero(lst[1]);
        assert(val == 0 || val == lst[1]);
        assert(val <= u32::MAX);
        assert(add_odd_evens(lst.skip(2)) <= (lst.len() as int / 2) * (u32::MAX as int));
        assert(add_odd_evens(lst) == val + add_odd_evens(lst.skip(2)));
    }
}

proof fn lemma_add_odd_evens_take(lst: Seq<u32>, i: int)
    requires
        0 <= i <= lst.len(),
        i % 2 == 0 || i % 2 == 1,
        lst.len() < u32::MAX,
    ensures
        i < 2 ==> add_odd_evens(lst.take(i)) == 0,
        i >= 2 ==> add_odd_evens(lst.take(i)) == add_odd_evens(lst.take(i - 2)) + odd_or_zero(lst[i - 1]),
    decreases i,
{
    if i < 2 {
        assert(add_odd_evens(lst.take(i)) == 0);
    } else {
        lemma_add_odd_evens_take(lst, i - 2);
        if i == 2 {
            assert(add_odd_evens(lst.take(i - 2)) == 0);
            assert(add_odd_evens(lst.take(i)) == odd_or_zero(lst[i - 1]));
        } else {
            let subseq = lst.take(i);
            let subseq_prev = lst.take(i - 2);
            assert(subseq.len() >= 2);
            assert(add_odd_evens(subseq) == odd_or_zero(subseq[1]) + add_odd_evens(subseq.skip(2)));
            assert(subseq.skip(2) == subseq_prev.skip(2));
            assert(add_odd_evens(subseq.skip(2)) == add_odd_evens(subseq_prev.skip(2)));
            assert(add_odd_evens(subseq) == add_odd_evens(subseq_prev) + odd_or_zero(lst[i - 1]));
        }
    }
}
// </vc-helpers>

// <vc-spec>
fn add(lst: Vec<u32>) -> (sum: u64)
    // pre-conditions-start
    requires
        0 < lst.len() < u32::MAX,
    // pre-conditions-end
    // post-conditions-start
    ensures
        sum == add_odd_evens(lst@),
    // post-conditions-end
// </vc-spec>

// <vc-code>
{
    let mut sum: u64 = 0;
    let mut i: usize = 1;
    while i < lst.len()
        invariant
            lst.len() < u32::MAX,
            0 <= i <= lst.len(),
            i % 2 == 1,
            sum <= u64::MAX,
            sum == add_odd_evens(lst@.take(i as int)),
        decreases lst.len() - i,
    {
        if lst[i] % 2 == 0 {
            let val = lst[i] as u64;
            proof {
                lemma_add_odd_evens_bounds(lst@);
                assert(add_odd_evens(lst@) <= (lst.len() as int / 2 + 1) * (u32::MAX as int));
                assert(val <= u32::MAX as u64);
                assert(sum + val <= u64::MAX);
            }
            sum = sum + val;
        }
        proof {
            if i + 2 <= lst.len() {
                lemma_add_odd_evens_take(lst@, (i + 2) as int);
            }
        }
        i = i + 2;
    }
    proof {
        if i >= lst.len() {
            assert(lst@.take(i as int) == lst@);
        }
    }
    sum
}
// </vc-code>

} // verus!
fn main() {}