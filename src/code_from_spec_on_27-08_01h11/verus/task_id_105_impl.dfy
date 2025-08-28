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
proof fn count_boolean_bounds(seq: Seq<bool>)
    ensures 0 <= count_boolean(seq) <= seq.len()
    decreases seq.len()
{
    if seq.len() == 0 {
    } else {
        count_boolean_bounds(seq.drop_last());
    }
}

proof fn count_boolean_prefix_property(seq: Seq<bool>, i: int)
    requires 0 <= i <= seq.len()
    ensures count_boolean(seq.subrange(0, i)) <= count_boolean(seq)
    decreases seq.len() - i
{
    if i == seq.len() {
        assert(seq.subrange(0, i) =~= seq);
    } else {
        count_boolean_prefix_property(seq, i + 1);
        let prefix_i = seq.subrange(0, i);
        let prefix_i_plus_1 = seq.subrange(0, i + 1);
        count_boolean_push_property(prefix_i, seq[i]);
        assert(prefix_i_plus_1 =~= prefix_i.push(seq[i]));
        assert(count_boolean(prefix_i_plus_1) == count_boolean(prefix_i) + if seq[i] { 1int } else { 0int });
        assert(count_boolean(prefix_i) <= count_boolean(prefix_i_plus_1));
    }
}

proof fn count_boolean_push_property(seq: Seq<bool>, elem: bool)
    ensures count_boolean(seq.push(elem)) == count_boolean(seq) + if elem { 1int } else { 0int }
    decreases seq.len()
{
    if seq.len() == 0 {
        assert(seq.push(elem) =~= seq![elem]);
    } else {
        let without_last = seq.drop_last();
        let last_elem = seq.last();
        assert(seq =~= without_last.push(last_elem));
        assert(seq.push(elem) =~= without_last.push(last_elem).push(elem));
        count_boolean_push_property(without_last, elem);
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
        count_boolean_bounds(arr@);
    }
    
    while i < arr.len()
        invariant
            0 <= i <= arr.len(),
            0 <= count <= i,
            count_boolean(arr@.subrange(0, i as int)) == count,
        decreases arr.len() - i
    {
        proof {
            let old_i = i;
            assert(arr@.subrange(0, old_i as int + 1) =~= arr@.subrange(0, old_i as int).push(arr@[old_i as int]));
            count_boolean_push_property(arr@.subrange(0, old_i as int), arr@[old_i as int]);
        }
        
        if arr[i] {
            count = count + 1;
        }
        
        i = i + 1;
    }
    
    proof {
        assert(arr@.subrange(0, i as int) =~= arr@);
    }
    
    count
}
// </vc-code>

} // verus!

fn main() {}