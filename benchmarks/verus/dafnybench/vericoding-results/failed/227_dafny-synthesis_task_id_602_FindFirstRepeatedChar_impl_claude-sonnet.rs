use vstd::prelude::*;

verus! {

// <vc-helpers>
fn lemma_no_repeat_before(s: Seq<char>, first_i: int, first_j: int)
    requires 
        0 <= first_i < first_j < s.len(),
        s[first_i] == s[first_j],
        forall|i: int, j: int| 0 <= i < j < first_j && s[i] == s[j] ==> i >= first_i
    ensures
        forall|i: int, j: int| 0 <= i < j < first_i ==> s[i] != s[j]
{
}

fn lemma_char_at_positions(s: Seq<char>, i: int, j: int, c: char)
    requires 0 <= i < j < s.len(), s[i] == c, s[j] == c
    ensures s[i] == s[j]
{
}
// </vc-helpers>

// <vc-spec>
fn find_first_repeated_char(s: &str) -> (result: (bool, char))
    ensures 
        (result.0 ==> exists|i: int, j: int| 0 <= i < j < s@.len() && s@[i] == s@[j] && s@[i] == result.1 && 
            (forall|k: int, l: int| 0 <= k < l < j && s@[k] == s@[l] ==> k >= i)) &&
        (!result.0 ==> (forall|i: int, j: int| 0 <= i < j < s@.len() ==> s@[i] != s@[j]))
// </vc-spec>
// <vc-code>
{
    let s_seq = s@;
    let mut i: usize = 0;
    
    while i < s_seq.len() as usize
        invariant
            0 <= i <= s_seq.len(),
            forall|k: int, l: int| 0 <= k < l < i ==> s@[k] != s@[l]
    {
        let mut j: usize = i + 1;
        let ghost char_i = s_seq[i as int];
        
        while j < s_seq.len() as usize
            invariant
                0 <= i < j <= s_seq.len(),
                forall|k: int, l: int| 0 <= k < l < i ==> s@[k] != s@[l],
                forall|l: int| i < l < j ==> s@[i as int] != s@[l]
        {
            let ghost char_j = s_seq[j as int];
            
            if char_i == char_j {
                assert(s@[i as int] == char_i);
                assert(s@[j as int] == char_j);
                assert(s@[i as int] == s@[j as int]);
                
                proof {
                    lemma_char_at_positions(s@, i as int, j as int, char_i);
                }
                
                return (true, char_i);
            }
            j += 1;
        }
        i += 1;
    }
    
    (false, 'a')
}
// </vc-code>

fn main() {}

}