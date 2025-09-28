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
#[verifier(external_body)]
#[spec]
fn count_char(s: Seq<char>, c: char) -> nat {
    s.filter(|x: char| x == c).len()
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
    let mut b_count: nat = 0;
    let mut a_count: nat = 0;
    let mut d_count: nat = 0;

    // Count occurrences of 'b', 'a', 'd'
    // This loop establishes the multiset equality between 'a' and 'b' (the result)
    // and also computes the counts needed for constructing 'b'.
    #[verifier::loop_invariant(
        0 <= i && i <= a.len(),
        b_count == count_char(a@.subsequence(0, i as nat), 'b'),
        a_count == count_char(a@.subsequence(0, i as nat), 'a'),
        d_count == count_char(a@.subsequence(0, i as nat), 'd'),
    )]
    for i in 0..a.len() {
        if a[i] == 'b' {
            b_count = b_count + 1;
        } else if a[i] == 'a' {
            a_count = a_count + 1;
        } else if a[i] == 'd' {
            d_count = d_count + 1;
        }
    }

    let mut result: Vec<char> = Vec::new();

    // Populate with 'b's
    #[verifier::loop_invariant(
        0 <= i && i <= b_count as int,
        result.len() == i as nat,
        forall|j: int| 0 <= j < i ==> result@.index(j) == 'b',
        count_char(result@, 'b') == i as nat,
        count_char(result@, 'a') == 0,
        count_char(result@, 'd') == 0,
        result@.to_multiset().subset_of(a@.to_multiset()),
    )]
    for i in 0..b_count {
        result.push('b');
    }

    // Populate with 'a's
    #[verifier::loop_invariant(
        b_count as int <= i as int && i as int <= (b_count + a_count) as int,
        result.len() == i as nat,
        forall|j: int| 0 <= j < b_count as int ==> result@.index(j) == 'b',
        forall|j: int| b_count as int <= j < i as int ==> result@.index(j) == 'a',
        count_char(result@, 'b') == b_count,
        count_char(result@, 'a') == (i - b_count) as nat,
        count_char(result@, 'd') == 0,
        result@.to_multiset().subset_of(a@.to_multiset()),
    )]
    for i in b_count..(b_count + a_count) {
        result.push('a');
    }

    // Populate with 'd's
    #[verifier::loop_invariant(
        (b_count + a_count) as int <= i as int && i as int <= (b_count + a_count + d_count) as int,
        result.len() == i as nat,
        forall|j: int| 0 <= j < b_count as int ==> result@.index(j) == 'b',
        forall|j: int| b_count as int <= j < (b_count + a_count) as int ==> result@.index(j) == 'a',
        forall|j: int| (b_count + a_count) as int <= j < i as int ==> result@.index(j) == 'd',
        count_char(result@, 'b') == b_count,
        count_char(result@, 'a') == a_count,
        count_char(result@, 'd') == (i - (b_count + a_count)) as nat,
        result@.to_multiset().subset_of(a@.to_multiset()),
    )]
    for i in (b_count + a_count)..(b_count + a_count + d_count) {
        result.push('d');
    }

    assert(result.len() == a.len()); // Total length must match
    assert(count_char(result@, 'b') == b_count);
    assert(count_char(result@, 'a') == a_count);
    assert(count_char(result@, 'd') == d_count);

    // Proof for multiset equality
    proof {
        assert(count_char(result@, 'b') == count_char(a@, 'b'));
        assert(count_char(result@, 'a') == count_char(a@, 'a'));
        assert(count_char(result@, 'd') == count_char(a@, 'd'));
        // Any other character count in result is 0. Since 'a' only contains 'b', 'a', 'd',
        // any other character count in 'a' is also 0.
        // Therefore, their multisets are equal.
        assert(result@.to_multiset() =~= a@.to_multiset());
    }

    // Proof for sortedbad
    proof {
        let s = result@;
        let s_len = s.len();

        // all b's are before all a's and d's
        // An element s[idx] == 'b' implies idx < b_count.
        // An element s[idx] == 'a' implies b_count <= idx < b_count + a_count.
        // An element s[idx] == 'd' implies b_count + a_count <= idx < s_len.
        
        assert(forall|i_idx: int, j_idx: int| #[trigger] (s[i_idx] == 'b') && (s[j_idx] == 'a' || s[j_idx] == 'd') && 0 <= i_idx < s_len && 0 <= j_idx < s_len ==> i_idx < j_idx) by {
            assert(b_count == count_char(s, 'b'));
            assert(a_count == count_char(s, 'a'));
            assert(d_count == count_char(s, 'd'));
            assert(b_count + a_count + d_count == s_len as nat);

            if s_len > 0 {
                assert(forall|idx: int| 0 <= idx < b_count ==> s[idx] == 'b');
                assert(forall|idx: int| b_count <= idx < b_count + a_count ==> s[idx] == 'a');
                assert(forall|idx: int| b_count + a_count <= idx < b_count + a_count + d_count ==> s[idx] == 'd');
            }

            if (0 <= i_idx && i_idx < s_len && 0 <= j_idx && j_idx < s_len && s[i_idx] == 'b' && s[j_idx] == 'a') {
                assert(i_idx < b_count as int);
                assert(j_idx >= b_count as int);
                assert(i_idx < j_idx);
            }
            if (0 <= i_idx && i_idx < s_len && 0 <= j_idx && j_idx < s_len && s[i_idx] == 'b' && s[j_idx] == 'd') {
                assert(i_idx < b_count as int);
                assert(j_idx >= (b_count + a_count) as int);
                assert(i_idx < j_idx);
            }
        };

        // all a's are after all b's
        assert(forall|i_idx: int, j_idx: int| #[trigger] (s[i_idx] == 'a') && (s[j_idx] == 'b') && 0 <= i_idx < s_len && 0 <= j_idx < s_len ==> i_idx > j_idx) by {
            // This is the contrapositive of "all b's are before all a's".
            // If i_idx <= j_idx, then either s[i_idx] is not 'a' or s[j_idx] is not 'b'.
            // Equivalently, if s[i_idx] == 'a' and s[j_idx] == 'b', then i_idx > j_idx.
            // We already proved: s[j_idx] == 'b' && s[i_idx] == 'a' ==> j_idx < i_idx, which is i_idx > j_idx.
            if (0 <= i_idx && i_idx < s_len && 0 <= j_idx && j_idx < s_len && s[i_idx] == 'a' && s[j_idx] == 'b') {
                assert(i_idx >= b_count as int);
                assert(j_idx < b_count as int);
                assert(i_idx > j_idx);
            }
        };

        // all a's are before all d's
        assert(forall|i_idx: int, j_idx: int| #[trigger] (s[i_idx] == 'a') && (s[j_idx] == 'd') && 0 <= i_idx < s_len && 0 <= j_idx < s_len ==> i_idx < j_idx) by {
            assert(forall|idx: int| s[idx] == 'a' ==> idx < (b_count + a_count) as int); // By construction of 'result'
            assert(forall|idx: int| s[idx] == 'd' ==> idx >= (b_count + a_count) as int); // By construction of 'result'
            // This implies i_idx < b_count + a_count <= j_idx, so i_idx < j_idx.
             if (0 <= i_idx && i_idx < s_len && 0 <= j_idx && j_idx < s_len && s[i_idx] == 'a' && s[j_idx] == 'd') {
                assert(i_idx < (b_count + a_count) as int);
                assert(j_idx >= (b_count + a_count) as int);
                assert(i_idx < j_idx);
            }
        };

        // all d's are after all b's and a's
        assert(forall|i_idx: int, j_idx: int| #[trigger] (s[i_idx] == 'd') && (s[j_idx] == 'a' || s[j_idx] == 'b') && 0 <= i_idx < s_len && 0 <= j_idx < s_len ==> i_idx > j_idx) by {
            // This is the contrapositive of "all a's and b's are before all d's".
            // If i_idx <= j_idx, then either s[i_idx] is not 'd' or (s[j_idx] is not 'a' and s[j_idx] is not 'b').
            // Equivalently, if s[i_idx] == 'd' and (s[j_idx] == 'a' or s[j_idx] == 'b'), then i_idx > j_idx.
            
            if (0 <= i_idx && i_idx < s_len && 0 <= j_idx && j_idx < s_len && s[i_idx] == 'd' && s[j_idx] == 'a') {
                assert(i_idx >= (b_count + a_count) as int);
                assert(j_idx < (b_count + a_count) as int);
                assert(i_idx > j_idx);
            }
            if (0 <= i_idx && i_idx < s_len && 0 <= j_idx && j_idx < s_len && s[i_idx] == 'd' && s[j_idx] == 'b') {
                assert(i_idx >= (b_count + a_count) as int);
                assert(j_idx < b_count as int);
                assert(i_idx > j_idx);
            }
        };
    }

    result
}
// </vc-code>

fn main() {}

}