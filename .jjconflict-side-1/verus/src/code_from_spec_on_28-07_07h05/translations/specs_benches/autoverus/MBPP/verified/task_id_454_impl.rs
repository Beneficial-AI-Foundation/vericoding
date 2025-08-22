use vstd::prelude::*;

fn main() {
    // Example usage of contains_z
    let text = b"hello world";
    let has_z = contains_z(text);
    println!("Text contains z/Z: {}", has_z);
}

verus! {

fn contains_z(text: &[u8]) -> (result: bool)
    ensures
        result == (exists|i: int| 0 <= i < text.len() && (text[i] == 90 || text[i] == 122)),
{
    let mut i = 0;
    /* code modified by LLM (iteration 1): added decreases clause to prove loop termination */
    while i < text.len()
        invariant
            0 <= i <= text.len(),
            forall|j: int| 0 <= j < i ==> text[j] != 90 && text[j] != 122,
        decreases text.len() - i,
    {
        if text[i] == 90 || text[i] == 122 {
            return true;
        }
        i += 1;
    }
    false
}

} // verus!