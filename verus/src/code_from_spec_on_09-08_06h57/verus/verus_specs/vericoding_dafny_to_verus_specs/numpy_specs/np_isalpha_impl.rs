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
    let mut result = Vec::new();
    
    for i in 0..input.len()
        invariant
            result.len() == i,
            forall|k: int| #![auto] 0 <= k < i ==> 
                result[k] == (input[k]@.len() > 0 && 
                             forall|j: int| #![auto] 0 <= j < input[k]@.len() ==> 
                                 is_alpha_char(input[k]@[j])),
    {
        let s = input[i];
        /* code modified by LLM (iteration 1): Fixed nat literal syntax and proper comparison */
        let mut is_all_alpha = s@.len() > 0;
        
        /* code modified by LLM (iteration 1): Fixed nat literal syntax */
        if s@.len() > 0 {
            /* code modified by LLM (iteration 1): Fixed loop range and sequence access */
            let s_len = s.len();
            for j in 0..s_len
                invariant
                    0 <= j <= s_len,
                    s_len == s@.len(),
                    is_all_alpha == forall|k: int| #![auto] 0 <= k < j ==> is_alpha_char(s@[k]),
            {
                /* code modified by LLM (iteration 1): Fixed sequence indexing using proper index method */
                if !check_alpha_char(s@.index(j as int)) {
                    is_all_alpha = false;
                    break;
                }
            }
        }
        
        result.push(is_all_alpha);
    }
    
    result
}

fn main() {}

}