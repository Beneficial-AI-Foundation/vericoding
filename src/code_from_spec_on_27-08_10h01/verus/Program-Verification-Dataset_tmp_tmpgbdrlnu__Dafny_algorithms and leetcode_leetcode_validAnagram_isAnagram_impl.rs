use vstd::prelude::*;
use vstd::multiset::*;

verus! {

proof fn to_multiset(s: &str) -> (mset: Multiset<char>)
    ensures mset == s@.to_multiset()
{
    assume(false);
    s@.to_multiset()
}

proof fn mset_equal(s: Multiset<char>, t: Multiset<char>) -> (equal: bool)
    ensures s == t <==> equal
{
    assume(false);
    true
}

// <vc-helpers>
spec fn char_count(s: Seq<char>, c: char) -> nat
    decreases s.len()
{
    if s.len() == 0 {
        0
    } else if s[0] == c {
        1 + char_count(s.subrange(1, s.len() as int), c)
    } else {
        char_count(s.subrange(1, s.len() as int), c)
    }
}

spec fn same_char_counts(s: Seq<char>, t: Seq<char>) -> bool {
    forall |c: char| char_count(s, c) == char_count(t, c)
}

proof fn multiset_equiv_char_counts(s: Seq<char>, t: Seq<char>)
    ensures s.to_multiset() == t.to_multiset() <==> same_char_counts(s, t)
{
}

proof fn multiset_len_eq(s: Seq<char>)
    ensures s.to_multiset().len() == s.len()
{
}

proof fn empty_multiset_eq()
    ensures Seq::<char>::empty().to_multiset() == Multiset::<char>::empty()
{
}

proof fn multiset_swap_invariant(v: Seq<char>, i: nat, j: nat)
    requires i < v.len() && j < v.len()
    ensures v.update(i, v[j as int]).update(j, v[i as int]).to_multiset() == v.to_multiset()
{
}

proof fn multiset_pop_property(v: Seq<char>)
    requires v.len() > 0
    ensures v.subrange(0, v.len() - 1).to_multiset().add(v[v.len() - 1]) == v.to_multiset()
{
}

proof fn remove_found_char_preserves_multiset(s_remaining: Seq<char>, t_vec: Seq<char>, c: char, j: nat)
    requires 
        j < t_vec.len(),
        t_vec[j as int] == c,
        s_remaining.len() > 0,
        s_remaining[0] == c
    ensures 
        s_remaining.subrange(1, s_remaining.len() as int).to_multiset() == 
        t_vec.update(j, t_vec[t_vec.len() - 1]).subrange(0, t_vec.len() - 1).to_multiset()
{
}
// </vc-helpers>

// <vc-spec>
// <vc-spec>
fn is_anagram(s: &str, t: &str) -> (equal: bool)
    ensures (s@.to_multiset() == t@.to_multiset()) == equal
// </vc-spec>
// </vc-spec>

// <vc-code>
{
    if s.len() != t.len() {
        proof {
            multiset_len_eq(s@);
            multiset_len_eq(t@);
        }
        return false;
    }
    
    if s.len() == 0 {
        proof {
            empty_multiset_eq();
        }
        return true;
    }
    
    let s_vec = s.chars().collect::<Vec<char>>();
    let mut t_vec = t.chars().collect::<Vec<char>>();
    
    let mut i = 0;
    while i < s_vec.len()
        invariant
            0 <= i <= s_vec@.len(),
            s_vec@.len() == t_vec@.len(),
            s_vec@ == s@,
            s_vec@.subrange(i as int, s_vec@.len() as int).to_multiset() == t_vec@.to_multiset()
    {
        let c = s_vec[i];
        let mut found = false;
        let mut j = 0;
        
        while j < t_vec.len()
            invariant
                0 <= j <= t_vec@.len(),
                t_vec@.len() >= 1,
                !found ==> forall |k: int| 0 <= k < j ==> t_vec@[k] != c,
                found ==> exists |k: int| 0 <= k < j && t_vec@[k] == c
        {
            if t_vec[j] == c {
                found = true;
                break;
            }
            j += 1;
        }
        
        if !found {
            return false;
        }
        
        proof {
            multiset_swap_invariant(t_vec@, j as nat, (t_vec.len() - 1) as nat);
        }
        t_vec.swap(j, t_vec.len() - 1);
        proof {
            multiset_pop_property(t_vec@);
            remove_found_char_preserves_multiset(
                s_vec@.subrange(i as int, s_vec@.len() as int),
                old(t_vec)@,
                c,
                j as nat
            );
        }
        t_vec.pop();
        i += 1;
    }
    
    proof {
        empty_multiset_eq();
    }
    
    true
}
// </vc-code>

fn main() {}

}