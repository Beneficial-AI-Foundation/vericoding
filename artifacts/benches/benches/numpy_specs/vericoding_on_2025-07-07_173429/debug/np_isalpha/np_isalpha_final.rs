use vstd::prelude::*;

verus! {

spec fn is_alpha_char(c: char) -> bool {
    ('A' <= c && c <= 'Z') || ('a' <= c && c <= 'z')
}

spec fn is_all_alpha_string(s: Seq<char>) -> bool {
    s.len() > 0 && forall|i: int| 0 <= i < s.len() ==> is_alpha_char(s[i])
}

fn is_alpha(input: &Vec<Vec<char>>) -> (ret: Vec<bool>)
    ensures
        ret.len() == input.len(),
        forall|i: int| 0 <= i < input.len() ==> 
            ret[i] == is_all_alpha_string(input[i]@),
{
    let mut ret = Vec::with_capacity(input.len());
    
    let mut i = 0;
    while i < input.len()
        invariant
            0 <= i <= input.len(),
            ret.len() == i,
            forall|k: int| 0 <= k < i ==> 
                ret[k] == is_all_alpha_string(input[k]@),
        decreases input.len() - i,
    {
        let current_string = &input[i];
        
        if current_string.len() == 0 {
            ret.push(false);
        } else {
            let mut j = 0;
            let mut is_all_alpha = true;
            
            while j < current_string.len() && is_all_alpha
                invariant
                    0 <= j <= current_string.len(),
                    is_all_alpha <==> forall|k: int| 0 <= k < j ==> is_alpha_char(current_string@[k]),
                decreases current_string.len() - j,
            {
                let c = current_string[j];
                if !(('A' <= c && c <= 'Z') || ('a' <= c && c <= 'z')) {
                    is_all_alpha = false;
                }
                j += 1;
            }
            ret.push(is_all_alpha);
        }
        i += 1;
    }
    
    ret
}

}