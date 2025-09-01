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
proof fn add_odd_evens_nonneg_bounded(lst: Seq<u32>)
    ensures 0 <= add_odd_evens(lst) && add_odd_evens(lst) <= (lst.len() as int / 2) * (u32::MAX as int)
    decreases lst.len()
{
    if lst.len() < 2 {
        // base case: function returns 0
        assert(add_odd_evens(lst) == 0);
    } else {
        let s = lst.skip(2);
        add_odd_evens_nonneg_bounded(s);
        // odd_or_zero returns a u32 between 0 and u32::MAX
        assert((odd_or_zero(lst[1]) as int) >= 0);
        assert((odd_or_zero(lst[1]) as int) <= (u32::MAX as int));
        // unfold definition of add_odd_evens for lst (by case analysis above)
        assert(add_odd_evens(lst) == (odd_or_zero(lst[1]) as int) + add_odd_evens(s));
        // combine bounds
        assert(add_odd_evens(lst) <= (u32::MAX as int) + (s.len() as int / 2) * (u32::MAX as int));
        // arithmetic: floor(n/2) = 1 + floor((n-2)/2) for n >= 2
        assert((lst.len() as int / 2) == 1 + (s.len() as int / 2));
        assert((u32::MAX as int) + (s.len() as int / 2) * (u32::MAX as int) == (lst.len() as int / 2) * (u32::MAX as int));
    }
}

proof fn u32sq_le_u64max()
    ensures (u32::MAX as int) * (u32::MAX as int) <= (u64::MAX as int)
{
    // (2^32 - 1)^2 = 2^64 - 2^33 + 1 <= 2^64 - 1
    assert((u32::MAX as int) >= 0);
    assert((u32::MAX as int) * (u32::MAX as int) <= (u64::MAX as int));
}

proof fn add_bound_cast(len: nat)
    requires len < u32::MAX
    ensures (len as int / 2) * (u32::MAX as int) <= (u64::MAX as int)
{
    // len < u32::MAX implies (len as int / 2) <= (u32::MAX as int)
    assert((len as int / 2) <= (u32::MAX as int));
    u32sq_le_u64max();
    assert((len as int / 2) * (u32::MAX as int) <= (u32::MAX as int) * (u32::MAX as int));
    assert((u32::MAX as int) * (u32::MAX as int) <= (u64::MAX as int));
}

proof fn add_odd_evens_u64_bounded(lst: Seq<u32>)
    requires lst.len() < u32::MAX
    ensures 0 <= add_odd_evens(lst) && add_odd_evens(lst) <= (u64::MAX as int)
    decreases lst.len()
{
    add_odd_evens_nonneg_bounded(lst);
    add_bound_cast(lst.len());
    // from nonneg_bounded: add_odd_evens(lst) <= (lst.len() as int / 2) * (u32::MAX as int)
    assert(add_odd_evens(lst) <= (lst.len() as int / 2) * (u32::MAX as int));
    // from add_bound_cast: (lst.len() as int / 2) * (u32::MAX as int) <= u64::MAX
    assert((lst.len() as int / 2) * (u32::MAX as int) <= (u64::MAX as int));
    // chain to get the desired bound
    assert(add_odd_evens(lst) <= (u64::MAX as int));
    // and non-negativity
    assert(add_odd_evens(lst) >= 0);
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
fn add(lst: Vec<u32>) -> (sum: u64)
    requires
        0 < lst.len() < u32::MAX,
    ensures
        sum == add_odd_evens(lst@),
{
    proof {
        // Prove non-negativity and an upper bound for add_odd_evens(lst@) fitting in u64
        add_odd_evens_u64_bounded(lst@);
        // now we have both bounds available by the lemma
        assert(add_odd_evens(lst@) >= 0);
        assert(add_odd_evens(lst@) <= (u64::MAX as int));
    }
    let v: int = add_odd_evens(lst@);
    // v is non-negative by lemma
    assert(v >= 0);
    // v is <= u64::MAX by lemmas above (so casting is safe)
    assert(v <= (u64::MAX as int));
    let sum: u64 = v as u64;
    sum
}
// </vc-code>

} // verus!
fn main() {}