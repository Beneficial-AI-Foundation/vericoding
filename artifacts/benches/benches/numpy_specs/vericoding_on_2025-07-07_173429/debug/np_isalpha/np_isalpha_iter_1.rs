use vstd::prelude::*;

verus! {

spec fn is_alpha_char(c: char) -> bool {
    ('A' <= c && c <= 'Z') || ('a' <= c && c <= 'z')
}

spec fn all_chars_alpha(s: Seq<char>) -> bool {
    forall|i: int| #![auto] 0 <= i < s.len() ==> is_alpha_char(s[i])
}

spec fn is_alpha_string_spec(s: Seq<char>) -> bool {
    s.len() > 0 && all_chars_alpha(s)
}

exec fn is_alpha_char_exec(c: char) -> (result: bool)
    ensures result == is_alpha_char(c)
{
    ('A' <= c && c <= 'Z') || ('a' <= c && c <= 'z')
}

fn is_alpha(input: Vec<Vec<char>>) -> (ret: Vec<bool>)
    ensures 
        ret.len() == input.len(),
        forall|i: int| #![auto] 0 <= i < input.len() ==> 
            ret[i] == is_alpha_string_spec(input[i]@)
{
    let mut ret = Vec::new();
    let mut i = 0usize;
    
    while i < input.len()
        invariant 
            0 <= i <= input.len(),
            ret.len() == i,
            forall|k: int| #![auto] 0 <= k < i ==> 
                ret[k] == is_alpha_string_spec(input[k]@)
        decreases input.len() - i
    {
        let current_chars = &input[i];
        
        if current_chars.len() == 0 {
            ret.push(false);
        } else {
            let mut j = 0usize;
            let mut is_all_alpha = true;
            
            while j < current_chars.len()
                invariant 
                    0 <= j <= current_chars.len(),
                    is_all_alpha <==> (forall|k: int| #![auto] 0 <= k < j ==> is_alpha_char(current_chars@[k]))
                decreases current_chars.len() - j
            {
                let current_char = current_chars[j];
                let is_current_alpha = is_alpha_char_exec(current_char);
                
                if !is_current_alpha {
                    is_all_alpha = false;
                }
                
                j = j + 1;
                
                proof {
                    if is_current_alpha {
                        assert(is_alpha_char(current_chars@[(j-1) as int]));
                        if is_all_alpha {
                            assert(forall|k: int| #![auto] 0 <= k < j-1 ==> is_alpha_char(current_chars@[k]));
                            assert(forall|k: int| #![auto] 0 <= k < j ==> is_alpha_char(current_chars@[k]));
                        }
                    } else {
                        assert(!is_alpha_char(current_chars@[(j-1) as int]));
                        assert(!(forall|k: int| #![auto] 0 <= k < j ==> is_alpha_char(current_chars@[k])));
                        assert(!is_all_alpha);
                    }
                }
            }
            
            proof {
                assert(j == current_chars.len());
                if is_all_alpha {
                    assert(forall|k: int| #![auto] 0 <= k < j ==> is_alpha_char(current_chars@[k]));
                    assert(forall|k: int| #![auto] 0 <= k < current_chars.len() ==> is_alpha_char(current_chars@[k]));
                    assert(all_chars_alpha(current_chars@));
                    assert(current_chars.len() > 0);
                    assert(is_alpha_string_spec(current_chars@));
                } else {
                    assert(!(forall|k: int| #![auto] 0 <= k < j ==> is_alpha_char(current_chars@[k])));
                    assert(!all_chars_alpha(current_chars@));
                    assert(!is_alpha_string_spec(current_chars@));
                }
            }
            
            ret.push(is_all_alpha);
        }
        i = i + 1;
    }
    
    ret
}

fn main() {}

}