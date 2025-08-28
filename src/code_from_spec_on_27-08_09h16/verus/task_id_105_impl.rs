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
proof fn lemma_count_boolean_bounds(seq: Seq<bool>)
    ensures 0 <= count_boolean(seq) <= seq.len()
    decreases seq.len()
{
    if seq.len() == 0 {
    } else {
        lemma_count_boolean_bounds(seq.drop_last());
    }
}

proof fn lemma_count_boolean_prefix(seq: Seq<bool>, i: int)
    requires 0 <= i <= seq.len()
    ensures count_boolean(seq.subrange(0, i)) <= count_boolean(seq)
    decreases seq.len() - i
{
    if i == seq.len() {
        assert(seq.subrange(0, i) =~= seq);
    } else {
        lemma_count_boolean_subrange_extend(seq, i);
        lemma_count_boolean_prefix(seq, i + 1);
        assert(count_boolean(seq.subrange(0, i)) <= count_boolean(seq.subrange(0, i + 1)));
        assert(count_boolean(seq.subrange(0, i + 1)) <= count_boolean(seq));
    }
}

proof fn lemma_count_boolean_push(seq: Seq<bool>)
    requires seq.len() > 0
    ensures count_boolean(seq) == count_boolean(seq.drop_last()) + if seq.last() { 1int } else { 0int }
{
}

proof fn lemma_count_boolean_subrange_extend(seq: Seq<bool>, i: int)
    requires 0 <= i < seq.len()
    ensures count_boolean(seq.subrange(0, i + 1)) == count_boolean(seq.subrange(0, i)) + if seq[i] { 1int } else { 0int }
{
    let prefix_i = seq.subrange(0, i);
    let prefix_i_plus_1 = seq.subrange(0, i + 1);
    
    assert(prefix_i_plus_1 =~= prefix_i.push(seq[i]));
    assert(prefix_i_plus_1.last() == seq[i]);
    assert(prefix_i_plus_1.drop_last() =~= prefix_i);
    
    lemma_count_boolean_push(prefix_i_plus_1);
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
        lemma_count_boolean_bounds(arr@);
    }
    
    while i < arr.len()
        invariant
            0 <= i <= arr.len(),
            0 <= count <= i,
            count == count_boolean(arr@.subrange(0, i as int)),
        decreases arr.len() - i
    {
        proof {
            lemma_count_boolean_subrange_extend(arr@, i as int);
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