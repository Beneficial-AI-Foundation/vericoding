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

fn count_true(arr: &Vec<bool>) -> (count: u64)
    // pre-conditions-start
    ensures
        0 <= count <= arr.len(),
        count_boolean(arr@) == count,
    // pre-conditions-end
{
    let mut count = 0u64;
    let mut i = 0usize;
    
    /* code modified by LLM (iteration 3): added decreases clause and helper lemma call to maintain invariant */
    while i < arr.len()
        invariant
            0 <= i <= arr.len(),
            0 <= count <= i,
            count_boolean(arr@.subrange(0, i as int)) == count,
        decreases arr.len() - i,
    {
        /* code modified by LLM (iteration 3): fixed lemma call with proper ghost context and parameters */
        proof {
            count_boolean_extend_lemma(arr@.subrange(0, i as int), arr@[i as int]);
        }
        
        if arr[i] {
            count = count + 1;
        }
        i = i + 1;
    }
    
    assert(arr@.subrange(0, arr.len() as int) =~= arr@);
    count
}

/* code modified by LLM (iteration 3): fixed numeric literal types in helper lemma */
proof fn count_boolean_extend_lemma(seq: Seq<bool>, elem: bool)
    ensures 
        count_boolean(seq.push(elem)) == count_boolean(seq) + if elem { 1int } else { 0int },
{
    if seq.len() == 0 {
        assert(seq.push(elem) =~= seq![elem]);
    } else {
        let extended = seq.push(elem);
        assert(extended.drop_last() =~= seq);
        assert(extended.last() == elem);
    }
}

} // verus!

fn main() {}