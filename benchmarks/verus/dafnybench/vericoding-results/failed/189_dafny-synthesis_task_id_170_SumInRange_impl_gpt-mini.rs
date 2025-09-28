use vstd::prelude::*;

verus! {

spec fn sum_to(a: Seq<int>, start: int, end: int) -> int
    recommends 
        0 <= start <= end <= a.len(),
    decreases end
    when 0 <= start <= end <= a.len()
{
    if start == end {
        0
    } else {
        sum_to(a, start, end - 1) + a[end - 1]
    }
}

// <vc-helpers>
// No helper lemmas required for this proof.
// </vc-helpers>

// <vc-spec>
fn sum_in_range(a: &[i32], start: usize, end: usize) -> (sum: i32)
    requires 
        start <= end <= a.len(),
    ensures
        sum == sum_to(a@.map(|i, v| v as int), start as int, end as int),
// </vc-spec>
// <vc-code>
{
    let seq = a@.map(|_, v: i32| v as int);
    let mut i: usize = start;
    let mut acc: i32 = 0;
    // establish loop invariants at entry
    assert((acc as int) == sum_to(seq, start as int, i as int));
    while i < end
        invariant { start <= i && i <= end }
        invariant { (acc as int) == sum_to(seq, start as int, i as int) }
        decreases { end - i }
    {
        let ai: i32 = a[i];
        // use the current invariant and the definition of sum_to to establish the invariant after the step
        assert((acc as int) == sum_to(seq, start as int, i as int));
        assert(seq@[i] == (ai as int));
        assert(sum_to(seq, start as int, i as int) + seq@[i] == sum_to(seq, start as int, (i + 1) as int));
        acc = acc + ai;
        i += 1;
        assert((acc as int) == sum_to(seq, start as int, i as int));
    }
    acc
}
// </vc-code>

fn main() {
}

}