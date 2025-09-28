use vstd::prelude::*;

verus! {

// <vc-helpers>
proof fn insert_before_each_lemma(s: Seq<String>, x: String, i: int, len: nat)
    requires
        0 <= i <= s.len(),
        len == 2 * i,
    ensures
        (#[trigger] seq_insert_before_each(s, x, i)).len() == 2 * i,
        forall|j: int| 0 <= j < i ==> 
            (#[trigger] seq_insert_before_each(s, x, i))[2*j] == x && 
            (#[trigger] seq_insert_before_each(s, x, i))[2*j + 1] == s@[j],
    decreases s.len() - i
{
    if i > 0 {
        let prev_i: int = i - 1;
        let prev_len: nat = 2 * prev_i as nat;
        insert_before_each_lemma(s, x, prev_i, prev_len);
        
        assert(seq_insert_before_each(s, x, i) =~= 
               seq_insert_before_each(s, x, prev_i).push(x).push(s@[prev_i as nat]));
        
        assert forall|j: int| 0 <= j < i implies 
            seq_insert_before_each(s, x, i)[2*j] == x && seq_insert_before_each(s, x, i)[2*j + 1] == s@[j] by {
            if j < prev_i {
                assert(seq_insert_before_each(s, x, prev_i)[2*j] == x);
                assert(seq_insert_before_each(s, x, prev_i)[2*j + 1] == s@[j]);
            } else {
                assert(j == prev_i);
            }
        }
    }
}

spec fn seq_insert_before_each(s: Seq<String>, x: String, count: int) -> Seq<String> {
    if count <= 0 {
        Seq::empty()
    } else {
        seq_insert_before_each(s, x, count - 1).push(x).push(s@[count - 1])
    }
}
// </vc-helpers>

// <vc-spec>
#[verifier::exec_allows_no_decreases_clause]
fn insert_before_each(s: Seq<String>, x: String) -> (v: Seq<String>)
    ensures
        v.len() == 2 * s.len(),
        forall|i: int| 0 <= i < s.len() ==> v[2*i] == x && v[2*i + 1] == s[i],
// </vc-spec>
// <vc-code>
{
    let mut v = Vec::<String>::new();
    let mut i: nat = 0;
    while i < s.len()
        invariant
            i <= s.len(),
            v@.len() == 2 * i,
            forall|j: nat| j < i ==> v@[2*j] == x && v@[2*j + 1] == s@[j],
        decreases s.len() - i
    {
        v.push(x.clone());
        v.push(s[i].clone());
        i = i + 1;
    }
    proof {
        insert_before_each_lemma(s, x, s.len() as int, 2 * s.len());
        assert(v@ =~= seq_insert_before_each(s, x, s.len() as int));
    }
    Seq::from_vec(v)
}
// </vc-code>

fn main() {}

}