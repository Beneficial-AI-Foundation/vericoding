use vstd::prelude::*;

fn main() {}

verus! {

fn replace_blanks_with_chars(str1: &[u8], ch: u8) -> (result: Vec<u8>)
    ensures
        str1@.len() == result@.len(),
        forall|i: int|
            0 <= i < str1.len() ==> result[i] == (if str1[i] == 32 {
                ch
            } else {
                str1[i]
            }),
{
    let mut out_str: Vec<u8> = Vec::with_capacity(str1.len());
    let mut index = 0;
    /* code modified by LLM (iteration 1): added decreases clause to prove loop termination */
    while index < str1.len()
        invariant
            0 <= index <= str1.len(),
            out_str.len() == index,
            forall|i: int| 0 <= i < index ==> out_str[i] == (if str1[i] == 32 { ch } else { str1[i] }),
        decreases str1.len() - index
    {
        if str1[index] == 32 {
            out_str.push(ch);
        } else {
            out_str.push(str1[index]);
        }
        index += 1;
    }
    out_str
}

} // verus!