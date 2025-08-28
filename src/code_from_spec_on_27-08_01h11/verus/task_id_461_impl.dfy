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
proof fn count_uppercase_recursively_bound(seq: Seq<char>)
    ensures 0 <= count_uppercase_recursively(seq) <= seq.len()
    decreases seq.len()
{
    if seq.len() == 0 {
    } else {
        count_uppercase_recursively_bound(seq.drop_last());
    }
}

proof fn count_uppercase_recursively_prefix(seq: Seq<char>, i: int)
    requires 0 <= i < seq.len()
    ensures count_uppercase_recursively(seq.subrange(0, i + 1)) == 
            count_uppercase_recursively(seq.subrange(0, i)) + if is_upper_case(seq[i]) { 1int } else { 0int }
    decreases seq.len() - i
{
    let prefix_i = seq.subrange(0, i);
    let prefix_i_plus_1 = seq.subrange(0, i + 1);
    
    assert(prefix_i_plus_1.last() == seq[i]);
    assert(prefix_i_plus_1.drop_last() =~= prefix_i);
}

fn is_upper_case_exec(c: char) -> (result: bool)
    ensures result == is_upper_case(c)
{
    (c as u32) >= 65 && (c as u32) <= 90
}
// </vc-helpers>

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
    
    proof {
        count_uppercase_recursively_bound(text@);
    }
    
    while i < text.len()
        invariant
            0 <= i <= text.len(),
            0 <= count <= i,
            count == count_uppercase_recursively(text@.subrange(0, i as int))
        decreases text.len() - i
    {
        proof {
            count_uppercase_recursively_prefix(text@, i as int);
        }
        
        if is_upper_case_exec(text[i]) {
            count = count + 1;
        }
        i = i + 1;
    }
    
    proof {
        assert(text@.subrange(0, text.len() as int) =~= text@);
    }
    
    count
}
// </vc-code>

} // verus!

fn main() {}