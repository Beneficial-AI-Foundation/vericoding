use vstd::prelude::*;

verus! {

// Helper function to create a repeated character sequence
spec fn repeat_char(ch: char, n: nat) -> Seq<char>
    decreases n
{
    if n == 0 {
        seq![]
    } else {
        seq![ch] + repeat_char(ch, (n - 1) as nat)
    }
}

// Helper function to decode RLE for postcondition
spec fn decode_rle(lst: Seq<(char, u32)>) -> Seq<char>
    decreases lst.len()
{
    if lst.len() == 0 {
        seq![]
    } else {
        let (ch, cnt) = lst[0];
        repeat_char(ch, cnt as nat) + decode_rle(lst.subrange(1, lst.len() as int))
    }
}

// Precondition (trivially true in this case)
spec fn run_length_encode_precond(s: Seq<char>) -> bool {
    true
}

// Postcondition matching the original Lean specification
spec fn run_length_encode_postcond(s: Seq<char>, result: Seq<(char, u32)>) -> bool {
    // All counts are positive
    (forall|i: int| 0 <= i < result.len() ==> (#[trigger] result.index(i)).1 > 0) &&
    // Adjacent pairs have different characters
    /* code modified by LLM (iteration 1): fixed trigger by separating arithmetic and non-arithmetic operations */
    (result.len() <= 1 || (forall|i: int| 0 <= i < result.len() - 1 ==> 
        result[i].0 != result[i + 1].0)) &&
    // Decoding gives back original string
    decode_rle(result) == s
}

// Helper function to decode RLE (executable version)
fn decode_rle_exec(lst: Vec<(char, u32)>) -> Vec<char> {
    let mut result = Vec::new();
    let mut i = 0;
    /* code modified by LLM (iteration 1): added decreases clause to while loop */
    while i < lst.len()
        decreases lst.len() - i
    {
        let (ch, cnt) = lst[i];
        let mut j = 0;
        /* code modified by LLM (iteration 1): added decreases clause to inner while loop */
        while j < cnt
            decreases cnt - j
        {
            result.push(ch);
            j += 1;
        }
        i += 1;
    }
    result
}

// Main run-length encode function
fn run_length_encode(s: Vec<char>) -> (result: Vec<(char, u32)>)
    requires run_length_encode_precond(s@)
    ensures run_length_encode_postcond(s@, result@)
{
    let mut result = Vec::new();
    
    if s.len() == 0 {
        return result;
    }
    
    let mut i = 0;
    /* code modified by LLM (iteration 1): added decreases clause to while loop */
    while i < s.len()
        invariant
            0 <= i <= s.len(),
            forall|j: int| 0 <= j < result.len() ==> result@[j].1 > 0,
            result.len() <= 1 || forall|j: int| 0 <= j < result.len() - 1 ==> 
                result@[j].0 != result@[j + 1].0,
            decode_rle(result@) == s@.subrange(0, i as int)
        decreases s.len() - i
    {
        let current_char = s[i];
        let mut count = 1u32;
        let mut j = i + 1;
        
        /* code modified by LLM (iteration 1): added decreases clause to inner while loop */
        while j < s.len() && s[j] == current_char
            invariant
                i < s.len(),
                i + 1 <= j <= s.len(),
                count == (j - i) as u32,
                count > 0,
                forall|k: int| i <= k < j ==> s@[k] == current_char
            decreases s.len() - j
        {
            count += 1;
            j += 1;
        }
        
        result.push((current_char, count));
        i = j;
    }
    
    result
}

fn main() {
}

} // verus!