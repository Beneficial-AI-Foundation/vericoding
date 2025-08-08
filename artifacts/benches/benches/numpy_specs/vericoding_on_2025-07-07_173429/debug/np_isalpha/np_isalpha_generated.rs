use vstd::prelude::*;

verus! {

spec fn is_alpha_char(c: char) -> bool {
    ('A' <= c && c <= 'Z') || ('a' <= c && c <= 'z')
}

fn is_alpha_char_exec(c: char) -> (result: bool)
    ensures result == is_alpha_char(c)
{
    ('A' <= c && c <= 'Z') || ('a' <= c && c <= 'z')
}

fn is_alpha(input: &Vec<Vec<char>>) -> (ret: Vec<bool>)
    ensures 
        ret.len() == input.len(),
        forall|i: int| #![auto] 0 <= i < input.len() ==> 
            ret[i] == (input[i].len() > 0 && forall|j: int| #![auto] 0 <= j < input[i].len() ==> 
                is_alpha_char(input[i][j])),
{
    let mut ret = Vec::with_capacity(input.len());
    
    let mut i: usize = 0;
    while i < input.len()
        invariant 
            i <= input.len(),
            ret.len() == i,
            forall|k: int| #![auto] 0 <= k < i as int ==> 
                ret[k] == (input[k].len() > 0 && forall|j: int| #![auto] 0 <= j < input[k].len() ==> 
                    is_alpha_char(input[k][j])),
        decreases input.len() - i,
    {
        if input[i].len() == 0 {
            ret.push(false);
        } else {
            let mut j: usize = 0;
            let mut is_all_alpha = true;
            let cur_string = &input[i];
            
            while j < cur_string.len() && is_all_alpha
                invariant 
                    j <= cur_string.len(),
                    cur_string.len() == input[i as int].len(),
                    is_all_alpha <==> forall|k: int| #![auto] 0 <= k < j as int ==> 
                        is_alpha_char(cur_string[k]),
                decreases cur_string.len() - j,
            {
                let ch = cur_string[j];
                if !is_alpha_char_exec(ch) {
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

fn main() {}

}