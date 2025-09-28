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
spec fn count_char(s: Seq<char>, c: char) -> nat {
    s.filter(|x: char| x == c).len()
}

proof fn lemma_multiset_preservation(original: Seq<char>, bs: Seq<char>, ads: Seq<char>)
    requires
        original.to_multiset() =~= bs.to_multiset().add(ads.to_multiset()),
        forall|i: int| 0 <= i < bs.len() ==> bs[i] == 'b',
        forall|i: int| 0 <= i < ads.len() ==> ads[i] == 'a' || ads[i] == 'd',
    ensures
        (bs + ads).to_multiset() =~= original.to_multiset(),
{
}

proof fn lemma_sortedbad_concat(bs: Seq<char>, ads: Seq<char>)
    requires
        forall|i: int| 0 <= i < bs.len() ==> bs[i] == 'b',
        forall|i: int| 0 <= i < ads.len() ==> ads[i] == 'a' || ads[i] == 'd',
        // ads is sorted (a's before d's)
        forall|i: int, j: int| 0 <= i < ads.len() && 0 <= j < ads.len() && ads[i] == 'a' && ads[j] == 'd' ==> i < j,
    ensures
        sortedbad(bs + ads),
{
    let result = bs + ads;
    assert forall|i: int, j: int| 0 <= i < result.len() && 0 <= j < result.len() && result[i] == 'b' && (result[j] == 'a' || result[j] == 'd') implies i < j by {
        if i < bs.len() && j >= bs.len() {
            assert(i < bs.len() <= j);
        }
    };
    
    assert forall|i: int, j: int| 0 <= i < result.len() && 0 <= j < result.len() && result[i] == 'a' && result[j] == 'b' implies i > j by {
        if i >= bs.len() && j < bs.len() {
            assert(i >= bs.len() > j);
        }
    };
    
    assert forall|i: int, j: int| 0 <= i < result.len() && 0 <= j < result.len() && result[i] == 'a' && result[j] == 'd' implies i < j by {
        if i >= bs.len() && j >= bs.len() {
            let i_ads = i - bs.len();
            let j_ads = j - bs.len();
            assert(ads[i_ads] == 'a' && ads[j_ads] == 'd');
            assert(i_ads < j_ads);
            assert(i < j);
        }
    };
    
    assert forall|i: int, j: int| 0 <= i < result.len() && 0 <= j < result.len() && result[i] == 'd' && (result[j] == 'a' || result[j] == 'b') implies i > j by {
        if i >= bs.len() && j < bs.len() {
            assert(i >= bs.len() > j);
        } else if i >= bs.len() && j >= bs.len() {
            let i_ads = i - bs.len();
            let j_ads = j - bs.len();
            if result[j] == 'a' {
                assert(ads[i_ads] == 'd' && ads[j_ads] == 'a');
                assert(j_ads < i_ads);
                assert(j < i);
            }
        }
    };
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
    let mut result = Vec::new();
    
    // First pass: collect all 'b's
    let mut i = 0;
    while i < a.len()
        invariant
            0 <= i <= a.len(),
            forall|k: int| 0 <= k < result.len() ==> result@[k] == 'b',
            result@.to_multiset().add(a@.subrange(i as int, a.len() as int).to_multiset()) =~= a@.to_multiset(),
        decreases a.len() - i,
    {
        if a[i] == 'b' {
            result.push('b');
        }
        i += 1;
    }
    
    // Second pass: collect all 'a's
    i = 0;
    while i < a.len()
        invariant
            0 <= i <= a.len(),
            forall|k: int| 0 <= k < result.len() ==> result@[k] == 'b' || result@[k] == 'a',
            result@.to_multiset().add(a@.subrange(i as int, a.len() as int).filter(|x: char| x == 'd').to_multiset()) =~= a@.to_multiset(),
        decreases a.len() - i,
    {
        if a[i] == 'a' {
            result.push('a');
        }
        i += 1;
    }
    
    // Third pass: collect all 'd's
    i = 0;
    while i < a.len()
        invariant
            0 <= i <= a.len(),
            forall|k: int| 0 <= k < result.len() ==> result@[k] == 'b' || result@[k] == 'a' || result@[k] == 'd',
            result@.to_multiset().add(a@.subrange(i as int, a.len() as int).filter(|x: char| x == 'd').to_multiset()) =~= a@.to_multiset(),
        decreases a.len() - i,
    {
        if a[i] == 'd' {
            result.push('d');
        }
        i += 1;
    }
    
    proof {
        // Split result into b's and non-b's for proof
        let bs_len = result@.filter(|x: char| x == 'b').len();
        let bs = result@.subrange(0, bs_len as int);
        let ads = result@.subrange(bs_len as int, result.len() as int);
        
        assert(forall|k: int| 0 <= k < bs.len() ==> bs[k] == 'b');
        assert(forall|k: int| 0 <= k < ads.len() ==> ads[k] == 'a' || ads[k] == 'd');
        assert(forall|i: int, j: int| 0 <= i < ads.len() && 0 <= j < ads.len() && ads[i] == 'a' && ads[j] == 'd' ==> i < j);
        lemma_sortedbad_concat(bs, ads);
        assert(result@ == bs + ads);
    }
    
    result
}
// </vc-code>

fn main() {}

}