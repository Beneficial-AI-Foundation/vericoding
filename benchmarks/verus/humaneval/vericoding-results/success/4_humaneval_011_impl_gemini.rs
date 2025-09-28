// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn is_binary_string(s: Seq<char>) -> bool {
    forall|i: int| 0 <= i < s.len() ==> s[i] == '0' || s[i] == '1'
}
// </vc-preamble>

// <vc-helpers>
fn xor_char_exec(c1: char, c2: char) -> (res: char)
    requires
        c1 == '0' || c1 == '1',
        c2 == '0' || c2 == '1',
    ensures
        res == '0' || res == '1',
        (c1 == c2 ==> res == '0'),
        (c1 != c2 ==> res == '1'),
{
    if c1 == c2 {
        '0'
    } else {
        '1'
    }
}
// </vc-helpers>

// <vc-spec>
fn string_xor(a: Vec<char>, b: Vec<char>) -> (result: Vec<char>)
    requires 
        a.len() == b.len(),
        is_binary_string(a@),
        is_binary_string(b@),
    ensures 
        result.len() == a.len(),
        is_binary_string(result@),
        forall|i: int| 0 <= i < a.len() as int ==> 
            (a@[i] == b@[i] ==> result@[i] == '0') &&
            (a@[i] != b@[i] ==> result@[i] == '1'),
// </vc-spec>
// <vc-code>
{
    let mut result = Vec::new();
    let mut i: usize = 0;
    while i < a.len()
        invariant
            i <= a.len(),
            a.len() == b.len(),
            is_binary_string(a@),
            is_binary_string(b@),
            result.len() == i,
            is_binary_string(result@),
            forall|j: int| 0 <= j < i as int ==> 
                (a@[j] == b@[j] ==> result@[j] == '0') &&
                (a@[j] != b@[j] ==> result@[j] == '1'),
        decreases a.len() - i
    {
        let char_a = a[i];
        let char_b = b[i];

        let xor_res = xor_char_exec(char_a, char_b);

        result.push(xor_res);
        i = i + 1;
    }
    result
}
// </vc-code>


}

fn main() {}