use vstd::prelude::*;

fn main() {
    // Example usage
    let text1 = b"hello";
    let text2 = b"hello Z world";
    let text3 = b"hello z world";
    
    println!("contains_z({:?}) = {}", std::str::from_utf8(text1).unwrap(), contains_z(text1));
    println!("contains_z({:?}) = {}", std::str::from_utf8(text2).unwrap(), contains_z(text2));
    println!("contains_z({:?}) = {}", std::str::from_utf8(text3).unwrap(), contains_z(text3));
}

verus! {

fn contains_z(text: &[u8]) -> (result: bool)
    ensures
        result == (exists|i: int| 0 <= i < text.len() && (text[i] == 90 || text[i] == 122)),
{
    let mut i = 0;
    /* code modified by LLM (iteration 1): Added decreases clause to fix verification error */
    while i < text.len()
        invariant
            0 <= i <= text.len(),
            forall|j: int| 0 <= j < i ==> !(text[j] == 90 || text[j] == 122),
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