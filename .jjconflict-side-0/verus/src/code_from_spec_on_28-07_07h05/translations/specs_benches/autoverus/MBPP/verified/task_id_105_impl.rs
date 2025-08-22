use vstd::prelude::*;

fn main() {
    // TODO: Remove this comment and implement the function body
}

verus! {

spec fn count_boolean(seq: Seq<bool>) -> int
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

/* code modified by LLM (iteration 3): fixed type annotation for seq![] comparison */
proof fn count_boolean_prefix_lemma(seq: Seq<bool>, i: int)
    requires 0 <= i < seq.len()
    ensures count_boolean(seq.take(i + 1)) == count_boolean(seq.take(i)) + if seq[i] { 1int } else { 0int }
    decreases seq.len() - i
{
    if i == 0 {
        assert(seq.take(1) == seq![seq[0]]);
        assert(seq.take(0) =~= seq![] as Seq<bool>);
    } else {
        let prefix_i = seq.take(i);
        let prefix_i_plus_1 = seq.take(i + 1);
        
        assert(prefix_i_plus_1.drop_last() == prefix_i);
        assert(prefix_i_plus_1.last() == seq[i]);
        
        count_boolean_prefix_lemma(seq, i - 1);
    }
}

fn count_true(arr: &Vec<bool>) -> (count: u64)
    ensures
        0 <= count <= arr.len(),
        count_boolean(arr@) == count,
{
    let mut count = 0u64;
    let mut i = 0;
    
    while i < arr.len()
        invariant
            0 <= i <= arr.len(),
            0 <= count <= i,
            count_boolean(arr@.take(i as int)) == count,
        decreases arr.len() - i,
    {
        /* code modified by LLM (iteration 2): added proof to maintain loop invariant */
        proof {
            count_boolean_prefix_lemma(arr@, i as int);
        }
        
        if arr[i] {
            count = count + 1;
        }
        i = i + 1;
    }
    
    assert(arr@.take(arr.len() as int) =~= arr@);
    count
}

} // verus!