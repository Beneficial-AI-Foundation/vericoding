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
proof fn count_uppercase_recursively_monotonic(seq: Seq<char>)
    ensures count_uppercase_recursively(seq) >= 0
    decreases seq.len()
{
    if seq.len() == 0 {
    } else {
        count_uppercase_recursively_monotonic(seq.drop_last());
    }
}

proof fn count_uppercase_recursively_bounded(seq: Seq<char>)
    ensures count_uppercase_recursively(seq) <= seq.len()
    decreases seq.len()
{
    if seq.len() == 0 {
    } else {
        count_uppercase_recursively_bounded(seq.drop_last());
    }
}

proof fn count_uppercase_recursively_subseq(seq: Seq<char>, i: int)
    requires 0 <= i <= seq.len()
    ensures count_uppercase_recursively(seq.subrange(0, i)) == 
            if i == 0 { 0int } else { 
                count_uppercase_recursively(seq.subrange(0, i - 1)) + 
                if is_upper_case(seq[i - 1]) { 1int } else { 0int }
            }
    decreases i
{
    if i == 0 {
    } else {
        assert(seq.subrange(0, i).drop_last() =~= seq.subrange(0, i - 1));
        assert(seq.subrange(0, i).last() == seq[i - 1]);
    }
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
    proof {
        count_uppercase_recursively_monotonic(text@);
        count_uppercase_recursively_bounded(text@);
    }
    
    let mut count: u64 = 0;
    let mut i: usize = 0;
    
    while i < text.len()
        invariant
            0 <= i <= text.len(),
            0 <= count <= i,
            count == count_uppercase_recursively(text@.subrange(0, i as int)),
    {
        proof {
            count_uppercase_recursively_subseq(text@, (i as int) + 1);
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