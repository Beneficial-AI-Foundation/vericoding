use vstd::prelude::*;

verus! {

spec fn is_lower_case(c: char) -> (result: bool) {
    (c as u32) >= 97 && (c as u32) <= 122
}
// pure-end
// pure-end

spec fn is_upper_case(c: char) -> (result: bool) {
    (c as u32) >= 65 && (c as u32) <= 90
}
// pure-end
// pure-end

spec fn count_uppercase_recursively(seq: Seq<char>) -> (result: int)
    decreases seq.len(),
{
    if seq.len() == 0 {
        0
    } else {
        count_uppercase_recursively(seq.drop_last()) + if is_upper_case(seq.last()) {
            1 as int
        } else {
            0 as int
        }
    }
}
// pure-end

// <vc-helpers>
fn is_upper_case_exec(c: char) -> (result: bool)
    ensures result == is_upper_case(c)
{
    let code = c as u32;
    code >= 65 && code <= 90
}

proof fn count_uppercase_recursively_drop_last_lemma(seq: Seq<char>, i: int)
    requires 0 <= i < seq.len()
    ensures count_uppercase_recursively(seq.subrange(0, i as int)) == count_uppercase_recursively(seq.subrange(0, (i + 1) as int)) - if is_upper_case(seq[i]) { 1int } else { 0int }
    decreases i
{
    if i == 0 {
        assert(seq.subrange(0, 1).drop_last() =~= Seq::<char>::empty());
    } else {
        count_uppercase_recursively_drop_last_lemma(seq, i - 1);
        assert(seq.subrange(0, i as int).drop_last() =~= seq.subrange(0, (i - 1) as int));
        assert(seq.subrange(0, (i + 1) as int).drop_last() =~= seq.subrange(0, i as int));
    }
}

proof fn count_uppercase_recursively_subrange_lemma(seq: Seq<char>, i: int)
    requires 0 <= i <= seq.len()
    ensures count_uppercase_recursively(seq.subrange(0, i)) == count_uppercase_recursively(seq.take(i))
    decreases i
{
    if i == 0 {
        assert(seq.subrange(0, 0) =~= Seq::<char>::empty());
        assert(seq.take(0) =~= Seq::<char>::empty());
    } else {
        count_uppercase_recursively_subrange_lemma(seq, i - 1);
        assert(seq.subrange(0, i).drop_last() =~= seq.subrange(0, i - 1));
        assert(seq.take(i).drop_last() =~= seq.take(i - 1));
        assert(seq.subrange(0, i).last() == seq[i - 1]);
        assert(seq.take(i).last() == seq[i - 1]);
    }
}
// </vc-helpers>

// <vc-description>
/*

*/
// </vc-description>

// <vc-spec>
fn count_uppercase(text: &Vec<char>) -> (count: u64)
    // post-conditions-start
    ensures
        0 <= count <= text.len(),
        count_uppercase_recursively(text@) == count,
    // post-conditions-end
// </vc-spec>

// <vc-code>
{
    let mut count: u64 = 0;
    let mut i: usize = 0;
    
    /* code modified by LLM (iteration 5): added decreases clause for loop termination */
    while i < text.len()
        invariant
            0 <= i <= text.len(),
            0 <= count <= i,
            count == count_uppercase_recursively(text@.take(i as int)),
        decreases text.len() - i
    {
        /* code modified by LLM (iteration 4): use executable function instead of spec function */
        if is_upper_case_exec(text[i]) {
            count = count + 1;
        }
        
        proof {
            count_uppercase_recursively_subrange_lemma(text@, (i + 1) as int);
            if is_upper_case(text@[i as int]) {
                assert(count_uppercase_recursively(text@.take((i + 1) as int)) == 
                       count_uppercase_recursively(text@.take(i as int)) + 1);
            } else {
                assert(count_uppercase_recursively(text@.take((i + 1) as int)) == 
                       count_uppercase_recursively(text@.take(i as int)));
            }
        }
        
        i = i + 1;
    }
    
    proof {
        assert(text@.take(text.len() as int) =~= text@);
    }
    
    count
}
// </vc-code>

} // verus!

fn main() {}