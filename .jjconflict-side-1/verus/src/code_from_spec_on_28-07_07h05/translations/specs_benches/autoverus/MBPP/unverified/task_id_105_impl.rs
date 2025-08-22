use vstd::prelude::*;

fn main() {}

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

/* code modified by LLM (iteration 4): added helper lemma to prove count_boolean property for push operation */
proof fn lemma_count_boolean_push(seq: Seq<bool>, b: bool)
    ensures count_boolean(seq.push(b)) == count_boolean(seq) + if b { 1int } else { 0int }
{
    if seq.len() == 0 {
        assert(seq.push(b).len() == 1);
        assert(seq.push(b).last() == b);
        assert(seq.push(b).drop_last() =~= seq);
    } else {
        assert(seq.push(b).last() == b);
        assert(seq.push(b).drop_last() =~= seq);
    }
}

fn count_true(arr: &Vec<bool>) -> (count: u64)
    ensures
        0 <= count <= arr.len(),
        count_boolean(arr@) == count,
{
    let mut count = 0u64;
    let mut i = 0;
    
    /* code modified by LLM (iteration 2): added proof annotations to maintain loop invariant */
    while i < arr.len()
        invariant
            0 <= i <= arr.len(),
            0 <= count <= i,
            count_boolean(arr@.subrange(0, i as int)) == count,
        decreases arr.len() - i,
    {
        /* code modified by LLM (iteration 4): simplified proof using helper lemma */
        let old_count = count;
        let old_i = i;
        
        if arr[i] {
            count = count + 1;
        }
        i = i + 1;
        
        // Prove that the invariant is maintained
        assert(arr@.subrange(0, i as int) == arr@.subrange(0, old_i as int).push(arr[old_i as int]));
        lemma_count_boolean_push(arr@.subrange(0, old_i as int), arr[old_i as int]);
        assert(count_boolean(arr@.subrange(0, old_i as int)) == old_count);
        /* code modified by LLM (iteration 4): fixed type annotation for integer literals */
        assert(count == old_count + if arr[old_i as int] { 1int } else { 0int });
    }
    
    assert(arr@.subrange(0, arr.len() as int) =~= arr@);
    count
}

} // verus!