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
proof fn count_uppercase_equivalence(seq: Seq<char>, i: int)
    requires 0 <= i <= seq.len()
    ensures count_uppercase_recursively(seq.take(i as int)) == count_uppercase_loop(seq, i)
    decreases i
{
    if i == 0 {
        assert(seq.take(0).len() == 0);
    } else {
        count_uppercase_equivalence(seq, i - 1);
        let prefix = seq.take(i as int);
        assert(prefix.drop_last() =~= seq.take(i - 1));
        assert(prefix.last() == seq[i - 1]);
    }
}

spec fn count_uppercase_loop(seq: Seq<char>, i: int) -> int
    decreases seq.len() - i
{
    if i >= seq.len() || i < 0 {
        0int
    } else {
        (if is_upper_case(seq[i]) { 1int } else { 0int }) + count_uppercase_loop(seq, i + 1)
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
    let mut count: u64 = 0;
    let mut i: usize = 0;
    
    while i < text.len()
        invariant
            0 <= i <= text.len(),
            0 <= count <= i,
            count == count_uppercase_loop(text@, i as int),
        decreases text.len() - i
    {
        if is_upper_case_exec(text[i]) {
            count = count + 1;
        }
        i = i + 1;
    }
    
    proof {
        count_uppercase_equivalence(text@, text.len() as int);
    }
    
    count
}
// </vc-code>

} // verus!

fn main() {}