use vstd::prelude::*;

fn main() {}

verus! {

spec fn is_lower_case(c: u8) -> bool {
    c >= 97 && c <= 122
}

spec fn is_upper_case(c: u8) -> bool {
    c >= 65 && c <= 90
}

/* code modified by LLM (iteration 2): added executable version of is_upper_case check */
fn is_upper_case_exec(c: u8) -> (result: bool)
    ensures result == is_upper_case(c)
{
    c >= 65 && c <= 90
}

spec fn count_uppercase_recursively(seq: Seq<u8>) -> int
    decreases seq.len(),
{
    if seq.len() == 0 {
        0int
    } else {
        count_uppercase_recursively(seq.drop_last()) + if is_upper_case(seq.last()) {
            /* code modified by LLM (iteration 2): added explicit int type suffix to fix compilation error */
            1int
        } else {
            /* code modified by LLM (iteration 2): added explicit int type suffix to fix compilation error */
            0int
        }
    }
}

/* code modified by LLM (iteration 2): added helper lemma for recursive count property */
proof fn lemma_count_uppercase_prefix(seq: Seq<u8>, i: int)
    requires 0 <= i < seq.len()
    ensures count_uppercase_recursively(seq.subrange(0, i + 1)) == 
            count_uppercase_recursively(seq.subrange(0, i)) + 
            if is_upper_case(seq[i]) { 1int } else { 0int }
    decreases seq.len() - i
{
    if i == 0 {
        assert(seq.subrange(0, 1) == seq![seq[0]]);
    } else {
        lemma_count_uppercase_prefix(seq, i - 1);
    }
}

fn count_uppercase(text: &[u8]) -> (count: u64)
    ensures
        0 <= count <= text.len(),
        count_uppercase_recursively(text@) == count,
{
    let mut count = 0u64;
    let mut i = 0;
    
    while i < text.len()
        invariant
            0 <= i <= text.len(),
            0 <= count <= i,
            count_uppercase_recursively(text@.subrange(0, i as int)) == count,
    {
        /* code modified by LLM (iteration 2): use executable version of is_upper_case */
        if is_upper_case_exec(text[i]) {
            count += 1;
        }
        i += 1;
        
        proof {
            /* code modified by LLM (iteration 2): fixed proof using helper lemma */
            lemma_count_uppercase_prefix(text@, (i - 1) as int);
        }
    }
    
    proof {
        assert(text@.subrange(0, text.len() as int) == text@);
    }
    
    count
}

} // verus!