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
    let mut i: usize = 0;
    let tracked mut spec_i: nat = 0;
    let tracked mut current_sum: int = 0;
    let mut found_negative: bool = false;
    while i < operations.len()
        invariant
            spec_i == i as nat,
            0 <= spec_i <= operations@.len(),
            current_sum == sum(operations@.take(spec_i).map(|_idx, j: i32| j as int)),
            found_negative <==> exists|j: int| 0 <= j < spec_i && sum(operations@.take(j + 1).map(|_idx, k: i32| k as int)) < 0,
    {
        let op = operations[i as usize];
        proof {
            current_sum = current_sum + (op as int);
            spec_i = spec_i + 1;
        }
        if current_sum < 0 {
            found_negative = true;
        }
        i = i + 1;
    }
    found_negative
}
// </vc-code>

fn main() {}
}