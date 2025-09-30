// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn is_binary_string(s: Seq<char>) -> bool {
    forall|i: int| 0 <= i < s.len() ==> s[i] == '0' || s[i] == '1'
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): added bit_xor_char with explicit ensures for XOR correctness and binary output */
fn bit_xor_char(x: char, y: char) -> (c: char)
    ensures
        (x == y ==> c == '0'),
        (x != y ==> c == '1'),
        c == '0' || c == '1',
{
    if x == y { '0' } else { '1' }
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
    /* code modified by LLM (iteration 2): implemented XOR loop with invariants and proofs using implies to avoid antecedent issue; proved binary result and pointwise spec */
    let n = a.len();
    let mut result_vec: Vec<char> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            a.len() == n,
            b.len() == n,
            i <= n,
            result_vec.len() == i,
            forall|j: int| 0 <= j < i as int ==>
                ((a@[j] == b@[j] ==> result_vec@[j] == '0') &&
                 (a@[j] != b@[j] ==> result_vec@[j] == '1')),
            forall|j: int| 0 <= j < i as int ==> (result_vec@[j] == '0' || result_vec@[j] == '1'),
        decreases (n - i) as int
    {
        let c = bit_xor_char(a[i], b[i]);
        result_vec.push(c);
        i += 1;
    }
    proof {
        assert(i == n);
        assert(result_vec.len() == i);

        // Prove result is a binary string
        assert forall|j: int| 0 <= j && j < result_vec.len() as int implies result_vec@[j] == '0' || result_vec@[j] == '1' by {
            assert(result_vec.len() == i);
            assert(0 <= j && j < i as int);
            assert(result_vec@[j] == '0' || result_vec@[j] == '1');
        };
        assert(is_binary_string(result_vec@));

        // Prove pointwise XOR specification
        assert forall|j: int| 0 <= j && j < a.len() as int implies
            ((a@[j] == b@[j] ==> result_vec@[j] == '0') &&
             (a@[j] != b@[j] ==> result_vec@[j] == '1')) by
        {
            assert(a.len() == n);
            assert(b.len() == n);
            assert(i == n);
            assert(0 <= j && j < i as int);
            assert(((a@[j] == b@[j] ==> result_vec@[j] == '0') && (a@[j] != b@[j] ==> result_vec@[j] == '1')));
        };
    }
    result_vec
}
// </vc-code>


}

fn main() {}