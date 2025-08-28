use vstd::prelude::*;

verus! {

spec fn count_boolean(seq: Seq<bool>) -> (result: int)
    decreases seq.len(),
{
    if seq.len() == 0 {
        0
    } else {
        count_boolean(seq.drop_last()) + if (seq.last()) {
            1 as int
        } else {
            0 as int
        }
    }
}
// pure-end

// <vc-helpers>
spec fn count_boolean_prefix(seq: Seq<bool>, i: nat) -> int
    decreases i
{
    if i == 0 {
        0
    } else if i <= seq.len() {
        count_boolean_prefix(seq, (i - 1) as nat) + if seq[(i - 1) as int] { 1int } else { 0int }
    } else {
        0
    }
}

proof fn count_boolean_equiv_prefix(seq: Seq<bool>)
    ensures count_boolean(seq) == count_boolean_prefix(seq, seq.len() as nat)
    decreases seq.len()
{
    if seq.len() == 0 {
    } else {
        count_boolean_equiv_prefix(seq.drop_last());
        assert(seq.drop_last() == seq.subrange(0, seq.len() - 1));
        assert(seq.last() == seq[seq.len() - 1]);
    }
}

proof fn count_boolean_prefix_monotonic(seq: Seq<bool>, i: nat, j: nat)
    requires i <= j <= seq.len()
    ensures count_boolean_prefix(seq, i) <= count_boolean_prefix(seq, j)
    decreases j - i
{
    if i == j {
    } else {
        count_boolean_prefix_monotonic(seq, i, (j - 1) as nat);
    }
}
// </vc-helpers>

// <vc-spec>
fn count_true(arr: &Vec<bool>) -> (count: u64)
    // pre-conditions-start
    ensures
        0 <= count <= arr.len(),
        count_boolean(arr@) == count,
    // pre-conditions-end
// </vc-spec>

// <vc-code>
{
    let mut count: u64 = 0;
    let mut i: usize = 0;
    
    proof {
        count_boolean_equiv_prefix(arr@);
    }
    
    while i < arr.len()
        invariant
            i <= arr.len(),
            count == count_boolean_prefix(arr@, i as nat),
            count <= i,
        decreases arr.len() - i
    {
        if arr[i] {
            count = count + 1;
        }
        i = i + 1;
        
        proof {
            count_boolean_prefix_monotonic(arr@, 0, i as nat);
        }
    }
    
    count
}
// </vc-code>

} // verus!

fn main() {}