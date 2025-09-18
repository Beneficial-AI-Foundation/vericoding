// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Added nat conversion helper for ghost code */
proof fn to_nat(x: usize) -> (y: nat)
    ensures y == x as nat
{ x as nat }
// </vc-helpers>

// <vc-spec>
spec fn is_whitespace_char(c: char) -> bool {
    c == ' ' || c == '\t' || c == '\n' || c == '\r' || c == '\x0c'
}

spec fn all_chars_whitespace(s: Seq<char>) -> bool 
    decreases s.len()
{
    if s.len() == 0 {
        true
    } else {
        is_whitespace_char(s[0]) && all_chars_whitespace(s.skip(1))
    }
}

fn isspace(a: Vec<String>) -> (result: Vec<bool>)
    ensures 
        result.len() == a.len(),
        forall|i: int| 0 <= i < a.len() ==> 
            result[i] == (a[i]@.len() > 0 && all_chars_whitespace(a[i]@)),
        forall|i: int| 0 <= i < a.len() ==> 
            (a[i]@.len() == 0 ==> result[i] == false),
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Fixed type mismatches and indexing in ghost code */
{
    let mut result = Vec::new();
    let mut i: usize = 0;
    while i < a.len()
        invariant
            0 <= i <= a.len(),
            result.len() == i,
            forall|j: int| 0 <= j < i ==> result[j] == (a[j]@.len() > 0 && all_chars_whitespace(a[j]@)),
            forall|j: int| 0 <= j < i ==> (a[j]@.len() == 0 ==> result[j] == false)
    {
        let s = a[i].clone();
        let s_seq = s@;
        
        if s_seq.len() == 0 {
            result.push(false);
        } else {
            let mut all_ws = true;
            let mut j: usize = 0;
            
            while j < s_seq.len()
                invariant
                    0 <= j <= s_seq.len(),
                    all_ws == (if j == 0 { true } else { all_chars_whitespace(s_seq.subrange(0, to_nat(j))) })
            {
                let c = s_seq[j];
                
                if !is_whitespace_char(c) {
                    all_ws = false;
                    break;
                }
                j += 1;
            }
            
            result.push(all_ws);
        }
        
        i += 1;
    }
    result
}
// </vc-code>

}
fn main() {}