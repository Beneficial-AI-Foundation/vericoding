// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn sortedbad(s: Seq<char>) -> bool {

    (forall|i: int, j: int| 0 <= i < s.len() && 0 <= j < s.len() && s[i] == 'b' && (s[j] == 'a' || s[j] == 'd') ==> i < j) &&

    (forall|i: int, j: int| 0 <= i < s.len() && 0 <= j < s.len() && s[i] == 'a' && s[j] == 'b' ==> i > j) &&

    (forall|i: int, j: int| 0 <= i < s.len() && 0 <= j < s.len() && s[i] == 'a' && s[j] == 'd' ==> i < j) &&

    (forall|i: int, j: int| 0 <= i < s.len() && 0 <= j < s.len() && s[i] == 'd' && (s[j] == 'a' || s[j] == 'b') ==> i > j)
}
// </vc-preamble>

// <vc-helpers>
proof fn lemma_sortedbad_concat(s_b: Seq<char>, s_a: Seq<char>, s_d: Seq<char>)
    requires
        forall|i: int| 0 <= i < s_b.len() ==> s_b[i] == 'b',
        forall|i: int| 0 <= i < s_a.len() ==> s_a[i] == 'a',
        forall|i: int| 0 <= i < s_d.len() ==> s_d[i] == 'd',
    ensures
        sortedbad(s_b + s_a + s_d),
{
}
// </vc-helpers>

// <vc-spec>
fn bad_sort(a: Vec<char>) -> (b: Vec<char>)
    requires
        forall|k: int| 0 <= k < a.len() ==> a[k] == 'b' || a[k] == 'a' || a[k] == 'd',
    ensures
        sortedbad(b@),
        a@.to_multiset() =~= b@.to_multiset(),
        a.len() == b.len(),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 3): fixed compilation errors in proof block */
    let mut b_vec: Vec<char> = Vec::new();
    let mut a_vec: Vec<char> = Vec::new();
    let mut d_vec: Vec<char> = Vec::new();
    let mut i: usize = 0;

    while i < a.len()
        invariant
            0 <= i <= a.len(),
            forall|j: int| 0 <= j < b_vec.len() ==> b_vec@[j] == 'b',
            forall|j: int| 0 <= j < a_vec.len() ==> a_vec@[j] == 'a',
            forall|j: int| 0 <= j < d_vec.len() ==> d_vec@[j] == 'd',
            a@.subrange(0, i as int).to_multiset() === (b_vec@.to_multiset() + a_vec@.to_multiset() + d_vec@.to_multiset()),
        decreases a.len() - i,
    {
        let char_at_i = a[i];

        if char_at_i == 'b' {
            b_vec.push(char_at_i);
        } else if char_at_i == 'a' {
            a_vec.push(char_at_i);
        } else {
            d_vec.push(char_at_i);
        }
        i = i + 1;
    }

    let s_b = b_vec@;
    let s_a = a_vec@;
    let s_d = d_vec@;

    let mut b = b_vec;
    b.append(&mut a_vec);
    b.append(&mut d_vec);

    proof {
        vstd::seq_lib::lemma_add_is_add_multiset(s_b, s_a);
        vstd::seq_lib::lemma_add_is_add_multiset(s_b + s_a, s_d);

        vstd::seq::lemma_len_is_size_of_multiset(a@);
        vstd::seq::lemma_len_is_size_of_multiset(b@);
        
        lemma_sortedbad_concat(s_b, s_a, s_d);
        vstd::seq::lemma_seq_add_assoc(s_b, s_a, s_d);
    }

    b
}
// </vc-code>

}
fn main() {}