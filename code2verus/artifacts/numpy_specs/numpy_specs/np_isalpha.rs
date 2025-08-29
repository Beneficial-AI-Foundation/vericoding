use vstd::prelude::*;

verus! {

spec fn is_alpha_char(c: char) -> bool {
    ('A' <= c && c <= 'Z') || ('a' <= c && c <= 'z')
}

fn check_alpha_char(c: char) -> (result: bool)
    ensures result == is_alpha_char(c)
{
    ('A' <= c && c <= 'Z') || ('a' <= c && c <= 'z')
}

fn is_alpha(input: &Vec<&str>) -> (ret: Vec<bool>)
    ensures 
        ret.len() == input.len(),
        forall|i: int| #![auto] 0 <= i < input.len() ==> 
            ret[i] == (input[i]@.len() > 0 && 
                       forall|j: int| #![auto] 0 <= j < input[i]@.len() ==> 
                           is_alpha_char(input[i]@[j])),
{
    let mut ret = Vec::new();
    let mut i = 0;
    
    while i < input.len()
        invariant 
            ret.len() == i,
            i <= input.len(),
            forall|k: int| #![auto] 0 <= k < i ==> 
                ret[k] == (input[k]@.len() > 0 && 
                           forall|j: int| #![auto] 0 <= j < input[k]@.len() ==> 
                               is_alpha_char(input[k]@[j])),
        decreases input.len() - i,
    {
        let current_string = input[i];
        let string_len = current_string.unicode_len();
        
        // Check if string is non-empty and all characters are alphabetic
        let mut is_alpha_val = string_len > 0;
        let mut j = 0;
        
        while j < string_len
            invariant 
                j <= string_len,
                string_len == current_string@.len(),
                is_alpha_val == (string_len > 0 && 
                                forall|k: int| #![auto] 0 <= k < j ==> is_alpha_char(current_string@[k])),
            decreases string_len - j,
        {
            let c = current_string.get_char(j);
            if !check_alpha_char(c) {
                is_alpha_val = false;
            }
            j += 1;
        }
        
        // After the loop, we need to prove the final condition
        assert(is_alpha_val == (string_len > 0 && 
                               forall|k: int| #![auto] 0 <= k < string_len ==> is_alpha_char(current_string@[k])));
        
        ret.push(is_alpha_val);
        i += 1;
    }
    
    ret
}

fn main() {}

}