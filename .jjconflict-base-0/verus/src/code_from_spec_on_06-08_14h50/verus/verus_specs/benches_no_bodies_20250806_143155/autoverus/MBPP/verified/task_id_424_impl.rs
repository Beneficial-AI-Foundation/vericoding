use vstd::prelude::*;

fn main() {
    // Example usage of extract_rear_chars
    let data = vec![
        vec![b'h', b'e', b'l', b'l', b'o'],
        vec![b'w', b'o', b'r', b'l', b'd'],
        vec![b'!']
    ];
    let rear_chars = extract_rear_chars(&data);
    println!("Rear characters: {:?}", rear_chars);
}

verus! {

fn extract_rear_chars(s: &Vec<Vec<u8>>) -> (result: Vec<u8>)
    requires
        forall|i: int| 0 <= i < s.len() ==> #[trigger] s[i].len() > 0,
    ensures
        s.len() == result.len(),
        forall|i: int| 0 <= i < s.len() ==> result[i] == #[trigger] s[i][s[i].len() - 1],
{
    let mut result = Vec::new();
    let mut i = 0;
    
    /* code modified by LLM (iteration 1): added decreases clause to prove loop termination */
    while i < s.len()
        invariant
            0 <= i <= s.len(),
            result.len() == i,
            forall|j: int| 0 <= j < i ==> result[j] == s[j][s[j].len() - 1],
        decreases s.len() - i
    {
        let rear_char = s[i][s[i].len() - 1];
        result.push(rear_char);
        i += 1;
    }
    
    result
}

} // verus!