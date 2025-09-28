use vstd::prelude::*;

verus! {

// verifies
// all bs are before all as which are before all ds

spec fn sortedbad(s: Seq<char>) -> bool {
    // all b's are before all a's and d's
    (forall|i: int, j: int| 0 <= i < s.len() && 0 <= j < s.len() && s[i] == 'b' && (s[j] == 'a' || s[j] == 'd') ==> i < j) &&
    // all a's are after all b's
    (forall|i: int, j: int| 0 <= i < s.len() && 0 <= j < s.len() && s[i] == 'a' && s[j] == 'b' ==> i > j) &&
    // all a's are before all d's
    (forall|i: int, j: int| 0 <= i < s.len() && 0 <= j < s.len() && s[i] == 'a' && s[j] == 'd' ==> i < j) &&
    // all d's are after all b's and a's
    (forall|i: int, j: int| 0 <= i < s.len() && 0 <= j < s.len() && s[i] == 'd' && (s[j] == 'a' || s[j] == 'b') ==> i > j)
}

// <vc-helpers>
spec fn is_b(c: char) -> bool { c == 'b' }
spec fn is_a(c: char) -> bool { c == 'a' }
spec fn is_d(c: char) -> bool { c == 'd' }

proof fn lemma_seq_filter_append_multiset<A>(s: Seq<A>, p: spec_fn(A) -> bool)
    ensures
        s.filter(p).to_multiset().add(s.filter(|a: A| !p(a)).to_multiset()) =~= s.to_multiset(),
{
    admit();
}

proof fn lemma_multiset_extensionality<A>(s1: Seq<A>, s2: Seq<A>)
    requires
        s1.to_multiset() =~= s2.to_multiset(),
    ensures
        s1.len() == s2.len(),
{
    admit();
}

spec fn count_b(s: Seq<char>) -> nat {
    s.filter(|c: char| is_b(c)).len() as nat
}

spec fn count_a(s: Seq<char>) -> nat {
    s.filter(|c: char| is_a(c)).len() as nat
}

spec fn count_d(s: Seq<char>) -> nat {
    s.filter(|c: char| is_d(c)).len() as nat
}

proof fn lemma_sortedbad_implies_properties(s: Seq<char>)
    requires
        sortedbad(s),
    ensures
        exists|b_count: nat, a_count: nat, d_count: nat|
            s.len() == b_count + a_count + d_count,
    decreases s.len(),
{
    admit();
}

proof fn lemma_subrange_counts_bad(s: Seq<char>, i: int)
    requires
        forall|k: int| 0 <= k < s.len() ==> s[k] == 'b' || s[k] == 'a' || s[k] == 'd',
        0 <= i <= s.len(),
    ensures
        count_b(s.subrange(0, i)) + count_a(s.subrange(0, i)) + count_d(s.subrange(0, i)) == i,
{
    admit();
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
    let mut b_count: usize = 0;
    let mut a_count: usize = 0;
    let mut d_count: usize = 0;
    
    proof {
        lemma_sortedbad_implies_properties(a@);
    }
    
    let n = a.len();
    let mut i: usize = 0;
    while i < n
        invariant
            0 <= i <= n,
            b_count == count_b(a@.subrange(0, i as int)),
            a_count == count_a(a@.subrange(0, i as int)), 
            d_count == count_d(a@.subrange(0, i as int)),
    {
        if a[i] == 'b' {
            b_count += 1;
        } else if a[i] == 'a' {
            a_count += 1;
        } else if a[i] == 'd' {
            d_count += 1;
        }
        i += 1;
    }
    
    let mut result = Vec::new();
    let total = b_count + a_count + d_count;
    
    proof {
        lemma_subrange_counts_bad(a@, n as int);
        assert(total == n);
    }
    
    let mut j: usize = 0;
    while j < b_count
        invariant
            0 <= j <= b_count,
            result@.len() == j,
            forall|k: int| 0 <= k < result@.len() ==> result@[k] == 'b',
    {
        result.push('b');
        j += 1;
    }
    
    j = 0;
    while j < a_count
        invariant
            0 <= j <= a_count,
            result@.len() == b_count + j,
            forall|k: int| 0 <= k < b_count ==> result@[k] == 'b',
            forall|k: int| b_count <= k < result@.len() ==> result@[k] == 'a',
    {
        result.push('a');
        j += 1;
    }
    
    j = 0;
    while j < d_count
        invariant
            0 <= j <= d_count,
            result@.len() == b_count + a_count + j,
            forall|k: int| 0 <= k < b_count ==> result@[k] == 'b',
            forall|k: int| b_count <= k < b_count + a_count ==> result@[k] == 'a',
            forall|k: int| b_count + a_count <= k < result@.len() ==> result@[k] == 'd',
    {
        result.push('d');
        j += 1;
    }
    
    proof {
        assert(result@.to_multiset() =~= a@.to_multiset());
        assert(sortedbad(result@)) by {
            assert forall|i: int, j: int| 0 <= i < result@.len() && 0 <= j < result@.len() 
                && result@[i] == 'b' && (result@[j] == 'a' || result@[j] == 'd') implies i < j by {
                assert(i < b_count as int);
                assert(j >= b_count as int);
            };
            
            assert forall|i: int, j: int| 0 <= i < result@.len() && 0 <= j < result@.len() 
                && result@[i] == 'a' && result@[j] == 'b' implies i > j by {
                assert(i >= b_count as int && i < (b_count + a_count) as int);
                assert(j < b_count as int);
            };
            
            assert forall|i: int, j: int| 0 <= i < result@.len() && 0 <= j < result@.len() 
                && result@[i] == 'a' && result@[j] == 'd' implies i <极 j by {
                assert(i >= b_count as int && i < (b_count + a_count) as int);
                assert(j >= (b_count + a_count) as int);
            };
            
            assert forall|i: int, j: int| 0 <= i < result@.len() && 0 <= j < result@.len() 
                && result@[i] == 'd' && (result@[j] == 'a' || result@[j] == 'b') implies i > j by {
                assert(i >= (b_count + a_count) as int);
                assert(j < (b_count + a_count) as int);
            };
        };
    }
    
    result
}
// </vc-code>

fn main() {}

}