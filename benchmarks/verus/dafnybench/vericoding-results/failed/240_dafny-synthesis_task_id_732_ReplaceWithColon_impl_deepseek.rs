use vstd::prelude::*;

verus! {

spec fn is_space_comma_dot(c: char) -> bool {
    c == ' ' || c == ',' || c == '.'
}

// <vc-helpers>
proof fn lemma_str_indexing(s: &str, i: int)
    requires
        0 <= i < s@.len(),
    ensures
        s@[i] == s.as_bytes()@[i] as char,
{
}

proof fn lemma_vec_to_seq<T>(v: &Vec<T>, i: int)
    requires
        0 <= i < v@.len(),
    ensures
        v@[i] == v[i],
{
}

spec fn char_to_u8(c: char) -> u8 {
    c as u8
}

proof fn lemma_bytes_to_char(bytes: &[u8], i: int)
    requires
        0 <= i < bytes@.len(),
    ensures
        bytes@[i] as char == (bytes[i] as char),
{
}

proof fn lemma_usize_to_int(i: usize) -> (j: int)
    ensures
        j == i as int,
{
    i as int
}

spec fn is_space_comma_dot_u8(b: u8) -> bool {
    is_space_comma_dot(b as char)
}

spec fn u8_to_char(b: u8) -> char {
    b as char
}
// </vc-helpers>
// </vc-helpers>

// <vc-spec>
fn replace_with_colon(s: &str) -> (v: String)
    ensures 
        v@.len() == s@.len(),
        forall|i: int| 0 <= i < s@.len() ==> {
            if is_space_comma_dot(s@[i]) {
                v@[i] == ':'
            } else {
                v@[i] == s@[i]
            }
        }
// </vc-spec>
// <vc-code>
{
    let mut result = Vec::new();
    let bytes = s.as_bytes();
    let len = bytes.len();
    let mut i: usize = 0;
    
    while i < len
        invariant
            i <= len,
            result@.len() == i,
            forall|j: int| 0 <= j < i ==> {
                let current_byte = bytes[j];
                if is_space_comma_dot_u8(current_byte) {
                    u8_to_char(result@[j]) == ':'
                } else {
                    u8_to_char(result@[j]) == u8_to_char(current_byte)
                }
            },
    {
        let current_byte = bytes[i];
        if is_space_comma_dot_u8(current_byte) {
            result.push(b':');
        } else {
            result.push(current_byte);
        }
        i += 1;
    }
    
    String::from_utf8(result).unwrap()
}
// </vc-code>

fn main() {}

}