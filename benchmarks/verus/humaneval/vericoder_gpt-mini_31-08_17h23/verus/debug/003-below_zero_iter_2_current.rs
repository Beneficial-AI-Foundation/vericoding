use vstd::prelude::*;

verus! {

spec fn sum(s: Seq<int>) -> (result:int)
    decreases s.len(),
{
    if s.len() == 0 {
        0
    } else {
        s[0] + sum(s.skip(1))
    }
}
// pure-end
// pure-end

spec fn sum_other_way(s: Seq<int>) -> (result:int)
    decreases s.len(),
{
    if s.len() == 0 {
        0
    } else {
        s[s.len() - 1] + sum_other_way(s.take(s.len() - 1))
    }
}
// pure-end

// <vc-helpers>
// Added no helper lemmas; kept empty as not required for this proof.
// </vc-helpers>

// <vc-spec>
fn below_zero(operations: Vec<i32>) -> (result: bool)
    // pre-conditions-start
    requires
        forall|i: int|
            0 <= i <= operations@.len() ==> sum(operations@.take(i).map(|_idx, j: i32| j as int))
                <= i32::MAX,
    // pre-conditions-end
    // post-conditions-start
    ensures
        result <==> exists|i: int|
            0 <= i <= operations@.len() && sum(operations@.take(i).map(|_idx, j: i32| j as int))
                < 0,
    // post-conditions-end
// </vc-spec>
// <vc-code>
{
    // impl-start
    let mut i: usize = 0usize;
    let mut running: int = 0;
    while i < operations.len() {
        invariant 0 <= (i as int) && (i as int) <= operations@.len();
        invariant running == sum(operations@.take(i as int).map(|_idx, j: i32| j as int));
        decreases operations.len() - i;
        {
            let val_ref = operations.get(i).unwrap();
            let val: i32 = *val_ref;
            // relate runtime element to spec-level sequence element
            assert((val as int) == operations@[i as int] as int);
            running = running + (val as int);
            i = i + 1;
            if running < 0 {
                return true;
            }
        }
    }
    false
    // impl-end
}
// </vc-code>

fn main() {}
}