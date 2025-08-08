use vstd::prelude::*;

verus! {

spec fn is_alpha_char(c: char) -> bool {
    ('A' <= c && c <= 'Z') || ('a' <= c && c <= 'z')
}

fn is_alpha(input: Vec<Vec<char>>) -> (ret: Vec<bool>)
    ensures 
        ret.len() == input.len()
{
    let mut result = Vec::new();
    let mut i: usize = 0;
    
    while i < input.len()
        invariant 
            0 <= i <= input.len(),
            result.len() == i
        decreases input.len() - i
    {
        let current_vec = &input[i];
        let has_content = current_vec.len() > 0;
        let mut all_alpha = has_content;
        
        if has_content {
            let mut j: usize = 0;
            
            while j < current_vec.len() && all_alpha
                invariant 
                    0 <= j <= current_vec.len()
                decreases current_vec.len() - j
            {
                let c = current_vec[j];
                let is_alpha_c = ('A' <= c && c <= 'Z') || ('a' <= c && c <= 'z');
                if !is_alpha_c {
                    all_alpha = false;
                }
                j += 1;
            }
        }
        
        result.push(all_alpha);
        i += 1;
    }
    
    result
}

fn main() {}

}