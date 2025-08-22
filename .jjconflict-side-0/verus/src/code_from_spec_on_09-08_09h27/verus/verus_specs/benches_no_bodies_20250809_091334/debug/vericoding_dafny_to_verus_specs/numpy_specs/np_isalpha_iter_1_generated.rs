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
    let mut idx = 0;
    
    while idx < input.len()
        invariant
            idx <= input.len(),
            result.len() == idx,
            forall|i: int| #![auto] 0 <= i < idx ==> 
                result[i] == (input[i]@.len() > 0 && 
                             forall|j: int| #![auto] 0 <= j < input[i]@.len() ==> 
                                 is_alpha_char(input[i]@[j])),
    {
        let s = input[idx];
        let mut is_all_alpha = s@.len() > 0;
        let mut char_idx = 0;
        
        while char_idx < s@.len() && is_all_alpha
            invariant
                char_idx <= s@.len(),
                is_all_alpha ==> forall|j: int| #![auto] 0 <= j < char_idx ==> 
                    is_alpha_char(s@[j]),
                !is_all_alpha ==> exists|j: int| #![auto] 0 <= j < char_idx && 
                    !is_alpha_char(s@[j]),
        {
            if !check_alpha_char(s@[char_idx]) {
                is_all_alpha = false;
            }
            char_idx += 1;
        }
        
        result.push(is_all_alpha);
        idx += 1;
    }
    
    result
}

fn main() {}

}