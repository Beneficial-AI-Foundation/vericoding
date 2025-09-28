// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn str_len(a: Vec<String>) -> (result: Vec<u8>)
    ensures
        result.len() == a.len(),
        forall|i: int| 0 <= i < a.len() ==> {
            &&& result[i] as nat == a[i]@.len()
            &&& result[i] as nat >= 0
            &&& (a[i]@.len() == 0 <==> a[i]@ == Seq::<char>::empty())
        }
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): fix compilation errors and proof logic */
{
    let mut result = Vec::new();
    let mut i: usize = 0;
    while i < a.len()
        invariant
            0 <= i <= a.len(),
            result.len() == i,
            forall|j: int| 0 <= j < i ==> result@[j] as nat == a@[j]@.len(),
        decreases a.len() - i
    {
        let s = &a[i];
        let s_str = s.as_str();

        let mut char_len: usize = 0;
        let mut byte_idx: usize = 0;

        proof {
            vstd::string::lemma_str_is_unicode(s_str);
        }

        while byte_idx < s_str.len()
            invariant
                s_str.is_utf8(),
                0 <= byte_idx <= s_str.len(),
                vstd::string::is_char_boundary(s_str, byte_idx),
                char_len == s.view().substring_bytes(0, byte_idx).len(),
            decreases s_str.len() - byte_idx
        {
            let c = vstd::string::get_char_utf8(s_str, byte_idx);
            proof {
                c.lemma_char_len_utf8_is_char_boundary();
            }
            char_len = char_len + 1;
            byte_idx = byte_idx + c.len_utf8();
        }
        
        proof {
            vstd::string::lemma_string_view_as_str(s);
            vstd::string::lemma_str_len_is_view_num_bytes(s_str);
            assert(s_str.len() == s.view().num_bytes());

            vstd::seq_lib::lemma_substring_bytes_full(s.view());
            assert(s.view().substring_bytes(0, s_str.len()) == s.view());

            assert(char_len == s@.len());
        }

        let len_u8 = char_len as u8;

        result.push(len_u8);
        i = i + 1;
    }
    result
}
// </vc-code>

}
fn main() {}