// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
spec fn char_swapcase(c: char) -> char {
    if c.is_ascii_lowercase() {
        (c as u8 - 32) as char
    } else if c.is_ascii_uppercase() {
        (c as u8 + 32) as char
    } else {
        c
    }
}
// </vc-helpers>

// <vc-spec>
spec fn char_swapcase(c: char) -> char;

spec fn string_swapcase(s: Seq<char>) -> Seq<char>
    decreases s.len()
{
    if s.len() == 0 {
        Seq::<char>::empty()
    } else {
        seq![char_swapcase(s[0])] + string_swapcase(s.skip(1))
    }
}

fn swapcase(a: Vec<String>) -> (result: Vec<String>)
    ensures
        result.len() == a.len(),
        forall|i: int| 0 <= i < a.len() ==> result[i]@.len() == a[i]@.len(),
        forall|i: int, j: int| 0 <= i < a.len() && 0 <= j < a[i]@.len() ==> 
            #[trigger] result[i]@[j] == char_swapcase(a[i]@[j])
// </vc-spec>
// <vc-code>
{
    let mut result = Vec::with_capacity(a.len());
    proof {
        assert(a.len() == 0 || a.len() == 1 || a.len() > 1);
    }
    
    for i in 0..a.len()
        invariant
            result.len() == i,
            forall|k: int| 0 <= k < i ==> result[k]@.len() == a[k]@.len(),
            forall|k: int, j: int| 0 <= k < i && 0 <= j < a[k]@.len() ==> 
                #[trigger] result[k]@[j] == char_swapcase(a[k]@[j])
    {
        let s = a[i].as_str();
        let mut swapped = String::with_capacity(s.len());
        
        for j in 0..s.len()
            invariant
                swapped.len() == j,
                forall|k: int| 0 <= k < j ==> swapped@[k] == char_swapcase(s@[k])
        {
            let c = s@[j];
            let swapped_char = char_swapcase(c);
            proof {
                assert(swapped_char == char_swapcase(s@[j]));
            }
            swapped.push(swapped_char);
        }
        
        proof {
            assert(swapped@.len() == s.len());
            assert(forall|k: int| 0 <= k < s.len() ==> swapped@[k] == char_swapcase(s@[k]));
        }
        result.push(swapped);
    }
    
    result
}
// </vc-code>

}
fn main() {}