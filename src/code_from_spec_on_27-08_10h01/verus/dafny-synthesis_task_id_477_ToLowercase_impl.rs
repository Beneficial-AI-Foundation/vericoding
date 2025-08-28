use vstd::prelude::*;

verus! {

spec fn is_upper_case(c: char) -> bool {
    65 <= c as int <= 90
}

spec fn is_upper_lower_pair(C: char, c: char) -> bool {
    (C as int) == (c as int) - 32
}

spec fn shift_32(c: char) -> char {
    (((c as int + 32) % 128) as u8) as char
}

// <vc-helpers>
spec fn to_lowercase_char(c: char) -> char {
    if is_upper_case(c) {
        shift_32(c)
    } else {
        c
    }
}

proof fn lemma_shift_32_creates_pair(c: char)
    requires is_upper_case(c)
    ensures is_upper_lower_pair(c, shift_32(c))
{
    assert(65 <= c as int <= 90);
    assert(shift_32(c) == (((c as int + 32) % 128) as u8) as char);
    assert(c as int + 32 <= 122);
    assert((c as int + 32) % 128 == c as int + 32);
    assert(c as int == (c as int + 32) - 32);
}

spec fn str_to_char_seq(s: &str) -> Seq<char>;

proof fn lemma_char_conversion(s: &str, chars: &Vec<char>)
    requires chars@.len() == s@.len(),
             forall|j: int| 0 <= j < chars@.len() ==> chars@[j] == s@[j]
    ensures forall|j: int| 0 <= j < chars@.len() ==> chars@[j] == s@[j]
{
}
// </vc-helpers>

// <vc-spec>
// <vc-spec>
#[verifier::exec_allows_no_decreases_clause]
fn to_lowercase(s: &str) -> (v: String)
    ensures
        v@.len() == s@.len(),
        forall|i: int| #![trigger s@[i]] 0 <= i < s@.len() ==> 
        {
            if is_upper_case(s@[i]) {
                is_upper_lower_pair(s@[i], v@[i])
            } else {
                v@[i] == s@[i]
            }
        }
// </vc-spec>
// </vc-spec>

// <vc-code>
{
    let mut result = Vec::<char>::new();
    let mut i = 0usize;
    let chars = Vec::<char>::new();
    let mut temp_chars = chars;
    
    let mut s_iter = 0usize;
    while s_iter < s@.len()
        invariant
            s_iter <= s@.len(),
            temp_chars@.len() == s_iter,
            forall|j: int| 0 <= j < temp_chars@.len() ==> temp_chars@[j] == s@[j]
    {
        temp_chars.push(s@[s_iter as int]);
        s_iter += 1;
    }
    
    let chars = temp_chars;
    
    while i < chars.len()
        invariant
            i <= chars.len(),
            result@.len() == i,
            chars@.len() == s@.len(),
            forall|j: int| #![trigger s@[j]] 0 <= j < i ==> 
            {
                if is_upper_case(s@[j]) {
                    is_upper_lower_pair(s@[j], result@[j])
                } else {
                    result@[j] == s@[j]
                }
            },
            forall|j: int| 0 <= j < chars@.len() ==> chars@[j] == s@[j]
    {
        let c = chars[i];
        let new_c = if is_upper_case(c) {
            proof {
                lemma_shift_32_creates_pair(c);
            }
            shift_32(c)
        } else {
            c
        };
        
        result.push(new_c);
        i += 1;
    }
    
    let mut result_string = String::new();
    let mut k = 0usize;
    while k < result.len()
        invariant
            k <= result.len(),
            result_string@.len() == k,
            forall|j: int| 0 <= j < k ==> result_string@[j] == result@[j]
    {
        result_string.push(result[k]);
        k += 1;
    }
    
    result_string
}
// </vc-code>

fn main() {
}

}