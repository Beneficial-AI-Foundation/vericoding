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
fn odd_or_zero_exec(x: u32) -> (ret: u32) {
    if x % 2 == 0 {
        x
    } else {
        0
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
            0 < lst.len(),
            sum == add_odd_evens(lst@.take(i as int).skip(1)) as u64, // Corrected invariant for sum
            i % 2 == 1,
            i <= lst.len(),
    {
        sum = sum + odd_or_zero_exec(lst[i]) as u64;
        proof {
            assert(odd_or_zero_exec(lst[i]) == odd_or_zero(lst@[i])); // Corrected indexing

            // Proving the invariant for the next iteration
            assert(sum == add_odd_evens(lst@.take(i as int).skip(1)) as u64); // Ensure current state
            let next_i = i + 2;
            if (next_i <= lst.len()) {
                assert(add_odd_evens(lst@.take(next_i as int).skip(1)) ==
                    (odd_or_zero(lst@[i]) + add_odd_evens(lst@.take(next_i as int).skip(i as int + 2)))
                );
            }
        }
        i = i + 2;
    }
    sum
}
// </vc-code>

} // verus!
fn main() {}