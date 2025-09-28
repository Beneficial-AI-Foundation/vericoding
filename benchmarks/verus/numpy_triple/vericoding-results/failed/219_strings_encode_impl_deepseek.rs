// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Fix type errors and indexing */
fn is_valid_utf8_char(c: char) -> (valid: bool)
    ensures
        valid == (c <= '\u{10FFFF}'),
{
    c <= '\u{10FFFF}'
}

fn char_to_bytes(c: char, encoding: Vec<char>, errors: Vec<char>) -> (bytes: Vec<u8>)
    requires
        errors@.len() as int > 0,
        encoding@.len() as int > 0,
    ensures
        bytes@.len() > 0,
        bytes@.len() == if is_valid_utf8_char(c) { c.len_utf8() as nat } else { errors@[0].len_utf8() as nat },
        forall|i: int| 0 <= i < bytes@.len() ==> bytes@[i] <= 255,
{
    if is_valid_utf8_char(c) {
        let mut buffer = [0u8; 4];
        let encoded = c.encode_utf8(&mut buffer);
        encoded.as_bytes().to_vec()
    } else {
        if errors@.len() as int > 0 {
            let mut buffer = [0u8; 4];
            let encoded = errors@[0 as int].encode_utf8(&mut buffer);
            encoded.as_bytes().to_vec()
        } else {
            let default_error = '?';
            let mut buffer = [0u8; 4];
            let encoded = default_error.encode_utf8(&mut buffer);
            encoded.as_bytes().to_vec()
        }
    }
}

spec fn vec_chars_to_bytes(s: Seq<char>) -> Seq<u8> {
    if s.len() == 0 {
        Seq::<u8>::empty()
    } else {
        vec_chars_to_bytes(s.drop_last()) + seq![s[s.len() - 1] as u8]
    }
}

proof fn deterministic_lemma(a1: Seq<char>, a2: Seq<char>, encoding: Seq<char>, errors: Seq<char>)
    requires
        a1 =~= a2,
        errors.len() > 0,
    ensures
        vec_chars_to_bytes(a1) =~= vec_chars_to_bytes(a2),
{
    if a1.len() == 0 {
        assert(vec_chars_to_bytes(a1) =~= Seq::empty());
        assert(vec_chars_to_bytes(a2) =~= Seq::empty());
    } else {
        deterministic_lemma(a1.drop_last(), a2.drop_last(), encoding, errors);
    }
}
// </vc-helpers>

// <vc-spec>
fn encode(a: Vec<Vec<char>>, encoding: Vec<char>, errors: Vec<char>) -> (result: Vec<Vec<u8>>)
    ensures
        result@.len() == a@.len(),
        /* Deterministic encoding: same input produces same output */
        forall|i: int, j: int| 0 <= i < a@.len() && 0 <= j < a@.len() && a@[i] == a@[j] ==> result@[i] == result@[j],
        /* Empty strings encode to empty byte arrays */
        forall|i: int| 0 <= i < a@.len() && a@[i].len() == 0 ==> result@[i].len() == 0,
        /* Non-empty strings produce non-empty byte arrays */
        forall|i: int| 0 <= i < a@.len() && a@[i].len() > 0 ==> result@[i].len() > 0,
        /* For UTF-8 encoding, encoded size is at least the string length */
        forall|i: int| 0 <= i < a@.len() ==> result@[i].len() >= a@[i].len(),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Fix nat vs int comparisons and indexing */
    let mut result: Vec<Vec<u8>> = Vec::new();
    let mut i: usize = 0;
    
    while i < a.len()
        invariant
            0 <= i as int <= a@.len(),
            result@.len() == i as int,
            forall|k: int| 0 <= k < i as int ==> result@[k].len() >= a@[k].len(),
            forall|k: int| 0 <= k < i as int && a@[k].len() == 0 ==> result@[k].len() == 0,
            forall|k: int| 0 <= k < i as int && a@[k].len() > 0 ==> result@[k].len() > 0,
            forall|k: int, l: int| 0 <= k < i as int && 0 <= l < i as int && a@[k] == a@[l] ==> result@[k] == result@[l],
    {
        let s = &a[i as usize];
        let mut encoded_row: Vec<u8> = Vec::new();
        let mut j: usize = 0;
        
        if s.len() == 0 {
            result.push(encoded_row);
            i += 1;
            continue;
        }
        
        while j < s.len()
            invariant
                0 <= j as int <= s@.len(),
                encoded_row@.len() >= j as int,
                forall|m: int| 0 <= m < j as int ==> encoded_row@[m] <= 255,
        {
            let c = s[j as usize];
            let bytes = char_to_bytes(c, encoding.clone(), errors.clone());
            
            let mut k: usize = 0;
            while k < bytes.len()
                invariant
                    0 <= k as int <= bytes@.len(),
                    encoded_row@.len() == old(encoded_row)@.len() + k as int,
            {
                encoded_row.push(bytes[k as usize]);
                k += 1;
            }
            
            j += 1;
        }
        
        proof {
            deterministic_lemma(s@, s@, encoding@, errors@);
        }
        
        result.push(encoded_row);
        i += 1;
    }
    
    result
}
// </vc-code>


}
fn main() {}