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
// Helper lemmas to prove the sorted property
proof fn lemma_sorted_construction(b_count: nat, a_count: nat, d_count: nat, result: Seq<char>)
    requires
        result.len() == b_count + a_count + d_count,
        forall|i: int| 0 <= i < b_count ==> result[i] == 'b',
        forall|i: int| b_count <= i < b_count + a_count ==> result[i] == 'a',
        forall|i: int| b_count + a_count <= i < result.len() ==> result[i] == 'd',
    ensures
        sortedbad(result),
{
    assert forall|i: int, j: int| 0 <= i < result.len() && 0 <= j < result.len() && result[i] == 'b' && (result[j] == 'a' || result[j] == 'd') implies i < j by {
        if result[i] == 'b' {
            assert(i < b_count);
            if result[j] == 'a' {
                assert(b_count <= j < b_count + a_count);
            } else if result[j] == 'd' {
                assert(b_count + a_count <= j);
            }
        }
    }
    
    assert forall|i: int, j: int| 0 <= i < result.len() && 0 <= j < result.len() && result[i] == 'a' && result[j] == 'b' implies i > j by {
        if result[i] == 'a' {
            assert(b_count <= i < b_count + a_count);
            if result[j] == 'b' {
                assert(j < b_count);
            }
        }
    }
    
    assert forall|i: int, j: int| 0 <= i < result.len() && 0 <= j < result.len() && result[i] == 'a' && result[j] == 'd' implies i < j by {
        if result[i] == 'a' {
            assert(b_count <= i < b_count + a_count);
            if result[j] == 'd' {
                assert(b_count + a_count <= j);
            }
        }
    }
    
    assert forall|i: int, j: int| 0 <= i < result.len() && 0 <= j < result.len() && result[i] == 'd' && (result[j] == 'a' || result[j] == 'b') implies i > j by {
        if result[i] == 'd' {
            assert(b_count + a_count <= i);
            if result[j] == 'a' {
                assert(b_count <= j < b_count + a_count);
            } else if result[j] == 'b' {
                assert(j < b_count);
            }
        }
    }
}

// Helper lemma for filter property when extending a sequence
proof fn lemma_filter_extend(s: Seq<char>, c: char, pred: char)
    ensures
        s.push(c).filter(|x: char| x == pred).len() == 
        if c == pred { s.filter(|x: char| x == pred).len() + 1 } 
        else { s.filter(|x: char| x == pred).len() }
{
    let extended = s.push(c);
    let filtered_s = s.filter(|x: char| x == pred);
    let filtered_extended = extended.filter(|x: char| x == pred);
    
    if c == pred {
        assert(filtered_extended.len() == filtered_s.len() + 1);
    } else {
        assert(filtered_extended.len() == filtered_s.len());
    }
}

// Helper lemma to prove multiset equality
proof fn lemma_multiset_equality(a: Seq<char>, result: Seq<char>, b_count: nat, a_count: nat, d_count: nat)
    requires
        a.len() == result.len(),
        result.len() == b_count + a_count + d_count,
        b_count == a.filter(|c: char| c == 'b').len(),
        a_count == a.filter(|c: char| c == 'a').len(),
        d_count == a.filter(|c: char| c == 'd').len(),
        forall|j: int| 0 <= j < b_count ==> result[j] == 'b',
        forall|j: int| b_count <= j < b_count + a_count ==> result[j] == 'a',
        forall|j: int| b_count + a_count <= j < result.len() ==> result[j] == 'd',
    ensures
        a.to_multiset() =~= result.to_multiset(),
{
    // Count characters in result
    let result_b_count = result.filter(|c: char| c == 'b').len();
    let result_a_count = result.filter(|c: char| c == 'a').len();
    let result_d_count = result.filter(|c: char| c == 'd').len();
    
    assert(result_b_count == b_count);
    assert(result_a_count == a_count);
    assert(result_d_count == d_count);
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
    
    // Count occurrences of each character
    for i in 0..a.len()
        invariant
            b_count + a_count + d_count == i,
            b_count == a@.take(i as int).filter(|c: char| c == 'b').len(),
            a_count == a@.take(i as int).filter(|c: char| c == 'a').len(),
            d_count == a@.take(i as int).filter(|c: char| c == 'd').len(),
    {
        let old_b_count = b_count;
        let old_a_count = a_count;
        let old_d_count = d_count;
        
        if a[i] == 'b' {
            b_count = b_count + 1;
            proof {
                lemma_filter_extend(a@.take(i as int), a@[i as int], 'b');
                lemma_filter_extend(a@.take(i as int), a@[i as int], 'a');
                lemma_filter_extend(a@.take(i as int), a@[i as int], 'd');
                assert(a@.take((i + 1) as int) =~= a@.take(i as int).push(a@[i as int]));
            }
        } else if a[i] == 'a' {
            a_count = a_count + 1;
            proof {
                lemma_filter_extend(a@.take(i as int), a@[i as int], 'b');
                lemma_filter_extend(a@.take(i as int), a@[i as int], 'a');
                lemma_filter_extend(a@.take(i as int), a@[i as int], 'd');
                assert(a@.take((i + 1) as int) =~= a@.take(i as int).push(a@[i as int]));
            }
        } else {
            d_count = d_count + 1;
            proof {
                // The precondition ensures a@[i] must be one of 'b', 'a', or 'd'
                // Since it's not 'b' and not 'a', it must be 'd'
                lemma_filter_extend(a@.take(i as int), a@[i as int], 'b');
                lemma_filter_extend(a@.take(i as int), a@[i as int], 'a');
                lemma_filter_extend(a@.take(i as int), a@[i as int], 'd');
                assert(a@.take((i + 1) as int) =~= a@.take(i as int).push(a@[i as int]));
            }
        }
    }
    
    assert(b_count + a_count + d_count == a.len());
    assert(a@.take(a.len() as int) =~= a@);
    assert(b_count == a@.filter(|c: char| c == 'b').len());
    assert(a_count == a@.filter(|c: char| c == 'a').len());
    assert(d_count == a@.filter(|c: char| c == 'd').len());
    
    // Build result vector
    let mut result: Vec<char> = Vec::new();
    
    // Add all 'b's
    for i in 0..b_count
        invariant
            result@.len() == i,
            forall|j: int| 0 <= j < i ==> result@[j] == 'b',
    {
        result.push('b');
    }
    
    // Add all 'a's
    for i in 0..a_count
        invariant
            result@.len() == b_count + i,
            forall|j: int| 0 <= j < b_count ==> result@[j] == 'b',
            forall|j: int| b_count <= j < b_count + i ==> result@[j] == 'a',
    {
        result.push('a');
    }
    
    // Add all 'd's
    for i in 0..d_count
        invariant
            result@.len() == b_count + a_count + i,
            forall|j: int| 0 <= j < b_count ==> result@[j] == 'b',
            forall|j: int| b_count <= j < b_count + a_count ==> result@[j] == 'a',
            forall|j: int| b_count + a_count <= j < b_count + a_count + i ==> result@[j] == 'd',
    {
        result.push('d');
    }
    
    assert(result@.len() == b_count + a_count + d_count);
    assert(result@.len() == a.len());
    assert(forall|j: int| 0 <= j < b_count ==> result@[j] == 'b');
    assert(forall|j: int| b_count <= j < b_count + a_count ==> result@[j] == 'a');
    assert(forall|j: int| b_count + a_count <= j < result@.len() ==> result@[j] == 'd');
    
    proof {
        lemma_sorted_construction(b_count as nat, a_count as nat, d_count as nat, result@);
        assert(sortedbad(result@));
        
        // Prove multiset equality
        lemma_multiset_equality(a@, result@, b_count as nat, a_count as nat, d_count as nat);
        assert(a@.to_multiset() =~= result@.to_multiset());
    }
    
    result
}
// </vc-code>

fn main() {}

}