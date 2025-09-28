use vstd::prelude::*;

verus! {

// <vc-helpers>
proof fn lemma_seq_ext_equal_len_multiset_equal<S>(s1: Seq<S>, s2: Seq<S>)
    requires
        s1.len() == s2.len(),
        s1.to_multiset() == s2.to_multiset(),
        forall|i: int| 0 <= i && i < s1.len() ==> s1[i] == s2[i],
    ensures
        s1 == s2,
{
}

proof fn lemma_seq_swap_properties<S>(s: Seq<S>, i: int, j: int, t: Seq<S>)
    requires
        0 <= i && i < s.len() && 0 <= j && j < s.len(),
        t.len() == s.len(),
        t[i] == s[j],
        t[j] == s[i],
        forall|k: int| 0 <= k && k != i && k != j && k < s.len() ==> t[k] == s[k],
    ensures
        s.to_multiset() == t.to_multiset(),
        forall|k: int| 0 <= k && k < s.len() ==> #[trigger] t.to_multiset().count(t[k]) == s.to_multiset().count(t[k]),
{
    assert(s.to_multiset() == t.to_multiset()) by {
        assert forall|e| s.to_multiset().count(e) == t.to_multiset().count(e) by {
            if e == s[i] {
                if i == j {
                    assert(t.to_multiset().count(e) == s.to_multiset().count(e));
                } else {
                    assert(t.to_multiset().count(e) == s.to_multiset().count(e));
                }
            } else if e == s[j] {
                if i == j {
                    assert(t.to_multiset().count(e) == s.to_multiset().count(e));
                } else {
                    assert(t.to_multiset().count(e) == s.to_multiset().count(e));
                }
            } else {
                assert(t.to_multiset().count(e) == s.to_multiset().count(e));
            }
        }
    };
}
// </vc-helpers>

// <vc-spec>
fn string_swap(s: Seq<char>, i: nat, j: nat) -> (t: Seq<char>)
    requires 
        i >= 0 && j >= 0 && s.len() >= 0,
        s.len() > 0 ==> i < s.len() && j < s.len(),
    ensures 
        s.to_multiset() == t.to_multiset(),
        s.len() == t.len(),
        s.len() > 0 ==> forall|k: nat| k != i && k != j && k < s.len() ==> t[k as int] == s[k as int],
        s.len() > 0 ==> t[i as int] == s[j as int] && t[j as int] == s[i as int],
        s.len() == 0 ==> t == s,
// </vc-spec>
// <vc-code>
{
    if s.len() == 0 {
        assert(s.len() == 0 ==> s == s);
        s
    } else {
        assert(i < s.len() && j < s.len());
        
        let mut result = Vec::<char>::new();
        let mut k: usize = 0;
        let s_len = s.len();
        
        while k < s_len
            invariant
                k <= s_len,
                result.len() == k,
                s.to_multiset() == result@.to_multiset().add(s.subrange(k, s_len).to_multiset()),
                forall|idx: int| 0 <= idx && idx < k as int ==> 
                    if idx == i as int { result@[idx] == s[j as int] }
                    else if idx == j as int { result@[idx] == s[i as int] }
                    else { result@[idx] == s[idx] },
        {
            proof {
                assert(k < s_len);
            }
            let current_char = if k == i {
                s[j as int]
            } else if k == j {
                s[i as int]
            } else {
                s[k as int]
            };
            
            result.push(current_char);
            k = k + 1;
        }
        
        let final_seq = result@;
        
        proof {
            assert(final_seq.len() == s.len());
            assert(s.len() > 0 ==> final_seq[i as int] == s[j as int]);
            assert(s.len() > 0 ==> final_seq[j as int] == s[i as int]);
            
            assert forall|k_idx: int| 0 <= k_idx && k_idx != i as int && k_idx != j as int && k_idx < s.len() 
                implies final_seq[k_idx] == s[k_idx] by {
                assert(k_idx < s.len());
            };
            
            lemma_seq_swap_properties(s, i as int, j as int, final_seq);
        }
        
        final_seq
    }
}
// </vc-code>

// string == Seq<char>
//give se2011 ass2 ex1.dfy

fn main() {}

}