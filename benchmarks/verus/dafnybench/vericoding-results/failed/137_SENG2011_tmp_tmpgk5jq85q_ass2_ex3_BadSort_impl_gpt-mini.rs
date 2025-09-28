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
spec fn count_seq(s: Seq<char>, ch: char) -> nat {
    if s.len() == 0 {
        0
    } else {
        count_seq(s.slice(0, s.len() - 1), ch) + if s[s.len() - 1] == ch { 1 } else { 0 }
    }
}

proof fn seq_count_cons_last(s: Seq<char>, ch: char)
    ensures s.len() > 0 ==> count_seq(s, ch) == count_seq(s.slice(0, s.len() - 1), ch) + (if s[s.len() - 1] == ch { 1 } else { 0 })
{
    // trivial by definition
}

proof fn seq_to_multiset_count_lemma(s: Seq<char>, ch: char)
    ensures s.to_multiset().count(ch) == count_seq(s, ch)
{
    if s.len() == 0 {
        // both sides are 0
    } else {
        let n = s.len();
        let s_init = s.slice(0, n - 1);
        let last = s[n - 1];

        // Inductive hypothesis
        seq_to_multiset_count_lemma(s_init, ch);

        proof {
            // By definition of to_multiset and count_seq, holds by induction.
        }
    }
}

proof fn count_seq_zero_if_no_element(s: Seq<char>, ch: char)
    ensures (forall|i: int| 0 <= i && i < s.len() ==> s[i] != ch) ==> count_seq(s, ch) == 0
{
    if s.len() == 0 {
        // trivial
    } else {
        let n = s.len();
        let s_init = s.slice(0, n - 1);
        // show predicate holds for s_init
        assert(forall|i: int| 0 <= i && i < s_init.len() ==> s_init[i] != ch); // follows from hypothesis
        count_seq_zero_if_no_element(s_init, ch);
        proof {
            // by definition count_seq(s,ch) == count_seq(s_init,ch) + (if last==ch {1} else {0})
            // last != ch by hypothesis, and count_seq(s_init,ch) == 0 by IH, so total 0
        }
    }
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
    // Partition input into three vectors preserving relative order, then concatenate.
    let mut bvec: Vec<char> = Vec::new();
    let mut avec: Vec<char> = Vec::new();
    let mut dvec: Vec<char> = Vec::new();

    let mut i: int = 0;
    while i < a.len()
        invariant 0 <= i && i <= a.len()
        invariant bvec.len() as int == count_seq(a@.slice(0, i), 'b')
        invariant avec.len() as int == count_seq(a@.slice(0, i), 'a')
        invariant dvec.len() as int == count_seq(a@.slice(0, i), 'd')
        invariant forall|t: int| 0 <= t && t < bvec.len() as int ==> bvec@[t as usize] == 'b'
        invariant forall|t: int| 0 <= t && t < avec.len() as int ==> avec@[t as usize] == 'a'
        invariant forall|t: int| 0 <= t && t < dvec.len() as int ==> dvec@[t as usize] == 'd'
    {
        // capture previous lengths
        let prev_b = bvec.len();
        let prev_a = avec.len();
        let prev_d = dvec.len();

        let ch: char = a@[i];
        if ch == 'b' {
            bvec.push('b');
        } else if ch == 'a' {
            avec.push('a');
        } else {
            // by precondition ch must be 'd' if not 'a' or 'b'
            dvec.push('d');
        }

        // update invariants: show counts increase appropriately
        proof {
            // Use lemma about count_seq on prefix extended by last element
            seq_count_cons_last(a@.slice(0, i + 1), 'b');
            seq_count_cons_last(a@.slice(0, i + 1), 'a');
            seq_count_cons_last(a@.slice(0, i + 1), 'd');

            // bvec
            if ch == 'b' {
                assert(bvec.len() == prev_b + 1);
                assert(bvec.len() as int == count_seq(a@.slice(0, i), 'b') + 1);
                assert(count_seq(a@.slice(0, i), 'b') + 1 == count_seq(a@.slice(0, i + 1), 'b'));
            } else {
                assert(bvec.len() == prev_b);
                assert(bvec.len() as int == count_seq(a@.slice(0, i), 'b'));
                assert(count_seq(a@.slice(0, i), 'b') == count_seq(a@.slice(0, i + 1), 'b'));
            }

            // avec
            if ch == 'a' {
                assert(avec.len() == prev_a + 1);
                assert(avec.len() as int == count_seq(a@.slice(0, i), 'a') + 1);
                assert(count_seq(a@.slice(0, i), 'a') + 1 == count_seq(a@.slice(0, i + 1), 'a'));
            } else {
                assert(avec.len() == prev_a);
                assert(avec.len() as int == count_seq(a@.slice(0, i), 'a'));
                assert(count_seq(a@.slice(0, i), 'a') == count_seq(a@.slice(0, i + 1), 'a'));
            }

            // dvec
            if ch == 'd' {
                assert(dvec.len() == prev_d + 1);
                assert(dvec.len() as int == count_seq(a@.slice(0, i), 'd') + 1);
                assert(count_seq(a@.slice(0, i), 'd') + 1 == count_seq(a@.slice(0, i + 1), 'd'));
            } else {
                assert(dvec.len() == prev_d);
                assert(dvec.len() as int == count_seq(a@.slice(0, i), 'd'));
                assert(count_seq(a@.slice(0, i), 'd') == count_seq(a@.slice(0, i + 1), 'd'));
            }

            // maintain element-type invariants
            if ch == 'b' {
                assert(bvec@[prev_b] == 'b');
            }
            if ch == 'a' {
                assert(avec@[prev_a] == 'a');
            }
            if ch == 'd' {
                assert(dvec@[prev_d] == 'd');
            }
        }

        i = i + 1;
    }

    // Now build result by concatenating bvec, avec, dvec
    let mut res: Vec<char> = Vec::new();

    let mut j: int = 0;
    while j < bvec.len()
        invariant 0 <= j && j <= bvec.len()
        invariant res.len() as int == j
        invariant count_seq(res@, 'b') == j
        invariant forall|t: int| 0 <= t && t < j ==> res@[t as usize] == bvec@[t as usize]
    {
        res.push(bvec@[j as usize]);
        proof {
            seq_count_cons_last(res@.slice(0, j + 1), 'b');
            assert(res@[j as usize] == 'b');
            assert(count_seq(res@, 'b') == j + 1);
            assert(res@[j as usize] == bvec@[j as usize]);
        }
        j = j + 1;
    }

    let b_len = bvec.len() as int;

    let mut k: int = 0;
    while k < avec.len()
        invariant 0 <= k && k <= avec.len()
        invariant res.len() as int == b_len + k
        invariant count_seq(res@, 'b') == b_len
        invariant count_seq(res@, 'a') == k
        invariant forall|t: int| 0 <= t && t < b_len ==> res@[t as usize] == bvec@[t as usize]
        invariant forall|t: int| 0 <= t && t < k ==> res@[(b_len + t) as usize] == avec@[t as usize]
    {
        res.push(avec@[k as usize]);
        proof {
            seq_count_cons_last(res@.slice(0, b_len + k + 1), 'a');
            seq_count_cons_last(res@.slice(0, b_len + k + 1), 'b');
            assert(avec@[k as usize] == 'a');
            assert(count_seq(res@, 'a') == k + 1);
            assert(count_seq(res@, 'b') == b_len);
            assert(res@[(b_len + k) as usize] == avec@[k as usize]);
        }
        k = k + 1;
    }

    let avec_len = avec.len() as int;

    let mut l: int = 0;
    while l < dvec.len()
        invariant 0 <= l && l <= dvec.len()
        invariant res.len() as int == b_len + avec_len + l
        invariant count_seq(res@, 'b') == b_len
        invariant count_seq(res@, 'a') == avec_len
        invariant count_seq(res@, 'd') == l
        invariant forall|t: int| 0 <= t && t < b_len ==> res@[t as usize] == bvec@[t as usize]
        invariant forall|t: int| 0 <= t && t < avec_len ==> res@[(b_len + t) as usize] == avec@[t as usize]
        invariant forall|t: int| 0 <= t && t < l ==> res@[(b_len + avec_len + t) as usize] == dvec@[t as usize]
    {
        res.push(dvec@[l as usize]);
        proof {
            seq_count_cons_last(res@.slice(0, b_len + avec_len + l + 1), 'd');
            seq_count_cons_last(res@.slice(0, b_len + avec_len + l + 1), 'a');
            seq_count_cons_last(res@.slice(0, b_len + avec_len +
// </vc-code>

fn main() {}

}