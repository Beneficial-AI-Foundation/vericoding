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
    let mut i = 0;
    
    while i < input.len()
        invariant
            i <= input.len(),
            result.len() == i,
            forall|k: int| #![auto] 0 <= k < i ==> 
                result[k] == (input[k]@.len() > 0 && 
                             forall|j: int| #![auto] 0 <= j < input[k]@.len() ==> 
                                 is_alpha_char(input[k]@[j])),
    {
        let s = input[i];
        /* code modified by LLM (iteration 1): Fixed indexing by using proper usize indexing and proof blocks */
        let mut is_valid = s@.len() > 0;
        let mut j: usize = 0;
        
        while j < s@.len() && is_valid
            invariant
                j <= s@.len(),
                is_valid ==> forall|k: int| #![auto] 0 <= k < j ==> is_alpha_char(s@[k]),
                !is_valid ==> exists|k: int| #![auto] 0 <= k < j && !is_alpha_char(s@[k]),
        {
            proof {
                assert(j < s@.len());
                assert(0 <= j as int < s@.len());
            }
            if !check_alpha_char(s@[j as int]) {
                is_valid = false;
            }
            j += 1;
        }
        
        /* code modified by LLM (iteration 1): Added proof block to establish postcondition */
        proof {
            if s@.len() == 0 {
                assert(!is_valid);
            } else if is_valid {
                assert(forall|k: int| #![auto] 0 <= k < s@.len() ==> is_alpha_char(s@[k]));
            }
        }
        
        result.push(is_valid);
        i += 1;
    }
    
    result
}

fn main() {}

}