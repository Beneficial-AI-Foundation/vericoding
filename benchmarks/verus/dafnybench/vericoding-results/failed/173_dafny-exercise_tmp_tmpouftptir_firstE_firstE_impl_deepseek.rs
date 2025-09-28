use vstd::prelude::*;

verus! {

// <vc-helpers>
proof fn lemma_seq_contains_index<A>(s: Seq<A>, val: A) -> (idx: int)
    requires
        s.contains(val),
    ensures
        0 <= idx < s.len(),
        s[idx] == val,
        forall|i: int| 0 <= i < idx ==> s[i] != val,
    decreases s.len()
{
    if s[0] == val {
        0
    } else {
        let subseq = s.subrange(1, s.len() as int);
        let sub_idx = lemma_seq_contains_index(subseq, val);
        sub_idx + 1
    }
}

proof fn lemma_seq_contains_index_correct<A>(s: Seq<A>, val: A)
    requires
        s.contains(val),
    ensures
        0 <= lemma_seq_contains_index(s, val) < s.len(),
        s[lemma_seq_contains_index(s, val)] == val,
        forall|i: int| 0 <= i < lemma_seq_contains_index(s, val) ==> s[i] != val,
{
    let idx = lemma_seq_contains_index(s, val);
}
// </vc-helpers>
// </vc-helpers>

// <vc-spec>
fn firstE(a: &[char]) -> (x: i32)
    ensures
        if a@.contains('e') {
            0 <= x < a@.len() && a@[x as int] == 'e' && 
            forall|i: int| 0 <= i < x ==> a@[i] != 'e'
        } else {
            x == -1
        }
// </vc-spec>
// <vc-code>
{
    let mut i: usize = 0;
    let n = a.len();
    while i < n
        invariant
            0 <= i <= n,
            forall|j: int| 0 <= j < i ==> a@[j] != 'e',
        decreases n - i
    {
        if a[i] == 'e' {
            assert(a@.contains('e'));
            assert(a@[i as int] == 'e');
            proof {
                lemma_seq_contains_index_correct(a@, 'e');
                let idx = lemma_seq_contains_index(a@, 'e');
                assert(0 <= idx < a@.len());
                assert(a@[idx] == 'e');
                assert(forall|j: int| 0 <= j < idx ==> a@[j] != 'e');
                assert(i as int >= idx ==> a@[idx] == 'e' && i as int != idx ==> a@[i as int] != 'e');
                assert(i as int <= idx ==> a@[i as int] == 'e' && i as int == idx);
            }
            assert(i as int == lemma_seq_contains_index(a@, 'e'));
            return i as i32;
        }
        i = i + 1;
    }
    -1
}
// </vc-code>

fn main() {
}

}