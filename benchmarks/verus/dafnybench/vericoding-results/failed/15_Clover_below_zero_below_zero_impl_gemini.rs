// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): no change to logic */
proof fn or_iff_implies_or_iff(a: bool, b: bool, c: bool)
    requires
        b <==> c,
    ensures
        (a || b) <==> (a || c),
{
}
// </vc-helpers>

// <vc-spec>
fn below_zero(operations: Vec<i32>) -> (result: (Vec<i32>, bool))
    ensures
        result.0.len() == operations.len() + 1,
        result.0[0] == 0,
        forall|i: int| 0 <= i < (result.0.len() - 1) as int ==> result.0[i + 1] == result.0[i] + operations[i],
        result.1 == true ==> exists|i: int| 1 <= i <= operations.len() as int && result.0[i] < 0,
        result.1 == false ==> forall|i: int| 0 <= i < result.0.len() as int ==> result.0[i] >= 0,
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): fixed sequence indexing and replaced 'assume' with 'assert' */
    let mut sums: Vec<i32> = Vec::new();
    sums.push(0);

    let mut found_negative = false;
    let mut i: usize = 0;

    while i < operations.len()
        invariant
            0 <= i <= operations.len(),
            sums@.len() == (i as nat) + 1,
            sums@[0] == 0,
            forall|j: int| 0 <= j < i as int ==> sums@[j + 1] == sums@[j] + operations@[j],
            found_negative <==> (exists|j: int| 1 <= j <= i as int && sums@[j] < 0),
        decreases operations.len() - i
    {
        let current_sum = sums[i];
        let op = operations[i];
        
        let new_sum = if let Some(s) = current_sum.checked_add(op) {
            s
        } else {
            assert(false);
            loop {}
        };

        let old_found_negative = found_negative;
        if new_sum < 0 {
            found_negative = true;
        }

        proof {
            let i_old = i as int;
            let sums_after_push = sums@.push(new_sum);

            let exists_before = exists|j: int| 1 <= j <= i_old && sums@[j] < 0;
            let exists_after = exists|j: int| 1 <= j <= i_old + 1 && sums_after_push[j] < 0;
            
            assert(exists_after <==> (exists_before || new_sum < 0));
            or_iff_implies_or_iff(new_sum < 0, old_found_negative, exists_before);
            assert(found_negative <==> exists_after);
        }
        
        sums.push(new_sum);
        i = i + 1;
    }

    (sums, found_negative)
}
// </vc-code>

}
fn main() {}