// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

/* helper modified by LLM (iteration 5): Fix type conversions and nat indexing issues */
proof fn lemma_skip_property(s: Seq<char>)
    requires
        s.len() > 0,
    ensures
        s.skip(1).len() == s.len() - 1,
    decreases s.len()
{
    if s.len() > 1 {
        lemma_skip_property(s.skip(1));
    }
}

proof fn lemma_all_chars_decimal_recursive_property(s: Seq<char>)
    ensures
        (s.len() > 0 && is_decimal_char(s[0]) && all_chars_decimal(s.skip(1))) <==> 
        all_chars_decimal(s),
        (s.len() == 0) <==> all_chars_decimal(s),
    decreases s.len()
{
    if s.len() > 0 {
        lemma_skip_property(s);
        lemma_all_chars_decimal_recursive_property(s.skip(1));
    }
}

proof fn lemma_subrange_len(s: Seq<char>, start: int, end: int)
    requires
        start <= end <= s.len(),
    ensures
        s.subrange(start, end).len() == end - start,
{
}

proof fn lemma_empty_subrange(s: Seq<char>)
    ensures
        s.subrange(0, 0) == Seq::<char>::empty(),
{
}

proof fn lemma_subrange_skip_relationship(s: Seq<char>, j: int)
    requires
        0 <= j <= s.len(),
    ensures
        s.subrange(0, j + 1).skip(1) == s.subrange(1, j + 1),
{
}

proof fn lemma_seq_empty_property()
    ensures
        Seq::<char>::empty().len() == 0,
{
}

// </vc-helpers>

// <vc-spec>
spec fn is_decimal_char(c: char) -> bool {
    ('0' <= c && c <= '9')
}

spec fn all_chars_decimal(s: Seq<char>) -> bool
    decreases s.len()
{
    if s.len() == 0 {
        true
    } else {
        is_decimal_char(s[0]) && all_chars_decimal(s.skip(1))
    }
}

fn isdecimal(a: Vec<String>) -> (result: Vec<bool>)
    ensures 
        result.len() == a.len(),
        forall|i: int| 0 <= i < a.len() ==> {
            &&& (result[i] == true <==> (a[i]@.len() > 0 && all_chars_decimal(a[i]@)))
            &&& (a[i]@ == Seq::<char>::empty() ==> result[i] == false)
        }
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Fix type conversion issues and nat usage */
    let mut result: Vec<bool> = Vec::new();
    let mut i: usize = 0;
    
    while i < a.len()
        invariant
            result.len() == i,
            forall|j: int| 0 <= j < i ==> {
                &&& (result[j] == true <==> (a[j]@.len() > 0 && all_chars_decimal(a[j]@)))
                &&& (a[j]@ == Seq::<char>::empty() ==> result[j] == false)
            },
        decreases a.len() - i
    {
        let s: &String = &a[i];
        proof {
            lemma_seq_empty_property();
            lemma_all_chars_decimal_recursive_property(s@);
        }
        
        let is_empty = s.is_empty();
        
        if is_empty {
            result.push(false);
        } else {
            let mut all_decimal = true;
            let mut j: int = 0;
            let chars_seq = s@;
            
            while j < s.len() as int
                invariant
                    0 <= j <= s.len() as int,
                    all_decimal == all_chars_decimal(chars_seq.subrange(0, j)),
                    forall|k: int| 0 <= k < j ==> is_decimal_char(chars_seq[k]),
                decreases s.len() as int - j
            {
                let c = s.as_bytes()[j as usize] as char;
                
                proof {
                    lemma_subrange_len(chars_seq, 0, j);
                    lemma_all_chars_decimal_recursive_property(chars_seq.subrange(0, j + 1));
                }
                
                if !('0' <= c && c <= '9') {
                    all_decimal = false;
                    break;
                }
                j += 1;
            }
            
            result.push(all_decimal);
        }
        
        i += 1;
    }
    
    result
}
// </vc-code>


}
fn main() {}