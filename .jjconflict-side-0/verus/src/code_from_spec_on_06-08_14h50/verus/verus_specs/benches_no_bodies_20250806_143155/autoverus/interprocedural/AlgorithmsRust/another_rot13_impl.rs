use vstd::prelude::*;
 
verus!{

  fn main() {
    // Empty main function as specified
  }

   fn init (in_string: &mut Vec<char>, out_string: &mut Vec<char>)
   ensures
        in_string@.len() == out_string@.len(),
   {
    /* code modified by LLM (iteration 2): Replace StrSlice with Vec<char> and use proper character vector initialization */
    // Create alphabet mappings for ROT13
    // Input: normal alphabet, Output: ROT13 shifted alphabet
    let input_chars = vec![
        'a', 'b', 'c', 'd', 'e', 'f', 'g', 'h', 'i', 'j', 'k', 'l', 'm',
        'n', 'o', 'p', 'q', 'r', 's', 't', 'u', 'v', 'w', 'x', 'y', 'z',
        'A', 'B', 'C', 'D', 'E', 'F', 'G', 'H', 'I', 'J', 'K', 'L', 'M',
        'N', 'O', 'P', 'Q', 'R', 'S', 'T', 'U', 'V', 'W', 'X', 'Y', 'Z'
    ];
    let output_chars = vec![
        'n', 'o', 'p', 'q', 'r', 's', 't', 'u', 'v', 'w', 'x', 'y', 'z',
        'a', 'b', 'c', 'd', 'e', 'f', 'g', 'h', 'i', 'j', 'k', 'l', 'm',
        'N', 'O', 'P', 'Q', 'R', 'S', 'T', 'U', 'V', 'W', 'X', 'Y', 'Z',
        'A', 'B', 'C', 'D', 'E', 'F', 'G', 'H', 'I', 'J', 'K', 'L', 'M'
    ];
    
    *in_string = input_chars;
    *out_string = output_chars;
   }

    pub fn encrypt(text: &mut Vec<char>, in_string: &Vec<char>, out_string: &Vec<char>)
    requires
        in_string@.len() == out_string@.len(),
    {
        /* code modified by LLM (iteration 3): Add decreases clauses to while loops for termination */
        let mut i = 0;
        while i < text.len()
        invariant
            i <= text.len(),
            in_string@.len() == out_string@.len(),
        decreases text.len() - i
        {
            let mut j = 0;
            let mut found = false;
            
            // Look for the character in the input mapping
            while j < in_string.len() && !found
            invariant
                j <= in_string.len(),
                in_string@.len() == out_string@.len(),
                i < text.len(),
            decreases in_string.len() - j
            {
                if text[i] == in_string[j] {
                    text.set(i, out_string[j]);
                    found = true;
                }
                j = j + 1;
            }
            
            // If character not found in mapping, leave it unchanged
            i = i + 1;
        }
    }

}