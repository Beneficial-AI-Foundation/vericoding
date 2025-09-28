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
proof fn lemma_concatenated_is_sortedbad(b_seq: Seq<char>, a_seq: Seq<char>, d_seq: Seq<char>)
    requires
        forall|i: int| 0 <= i < b_seq.len() ==> b_seq[i] == 'b',
        forall|i: int| 0 <= i < a_seq.len() ==> a_seq[i] == 'a',
        forall|i: int| 0 <= i < d_seq.len() ==> d_seq[i] == 'd',
    ensures
        sortedbad(b_seq + a_seq + d_seq),
{
    let s = b_seq + a_seq + d_seq;
    let len_b = b_seq.len();
    let len_a = a_seq.len();
    let len_d = d_seq.len();

    assert(forall|i: int, j: int|
        0 <= i < s.len() && 0 <= j < s.len() && 
        s[i] == 'b' && (s[j]=='a' || s[j]=='d') ==>
        {
            assert(i < len_b) by {
                if i >= len_b {
                    if i < len_b + len_a {
                        assert(s[i] == 'a');
                    } else {
                        assert(s[i] == 'd');
                    }
                }
            };
            assert(j >= len_b) by {
                if j < len_b {
                    assert(s[j] == 'b');
                }
            };
            i < len_b && j >= len_b ==> i < j
        });

    assert(forall|i: int, j: int|
        0 <= i < s.len() && 0 <= j < s.len() && 
        s[i]=='a' && s[j]=='b' ==>
        {
            assert(i >= len_b && i < len_b + len_a) by {
                if i < len_b {
                    assert(s[i] == 'b');
                } else if i >= len_b + len_a {
                    assert(s[i] == 'd');
                }
            };
            assert(j < len_b) by {
                if j >= len_b {
                    if j < len_b + len_a {
                        assert(s[j] == 'a');
                    } else {
                        assert(s[j] == 'd');
                    }
                }
            };
            i >= len_b && j < len_b ==> i > j
        });

    assert(forall|i: int, j: int|
        0 <= i < s.len() && 0 <= j < s.len() && 
        s[i]=='a' && s[j]=='d' ==>
        {
            assert(i < len_b + len_a) by {
                if i >= len_b + len_a {
                    assert(s[i] == 'd');
                }
            };
            assert(j >= len_b + len_a) by {
                if j < len_b + len_a {
                    if j < len_b {
                        assert(s[j] == 'b');
                    } else {
                        assert(s[j] == 'a');
                    }
                }
            };
            i < len_b + len_a && j >= len_b + len_a ==> i < j
        });

    assert(forall|i: int, j: int|
        0 <= i < s.len() && 0 <= j < s.len() && 
        s[i]=='d' && (s[j]=='a' || s[j]=='b') ==>
        {
            assert(i >= len_b + len_a) by {
                if i < len_b + len_a {
                    if i < len_b {
                        assert(s[i] == 'b');
                    } else {
                        assert(s[i] == 'a');
                    }
                }
            };
            assert(j < len_b + len_a) by {
                if j >= len_b + len_a {
                    assert(s[j] == 'd');
                }
            };
            i >= len_b + len_a && j < len_b + len_a ==> i > j
        });
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
    let mut count_b = 0;
    let mut count_a = 0;
    let mut count_d = 0;

    for i in 0..a.len()
        invariant
            count_b + count_a + count_d == i,
            count_b <= i,
            count_a <= i,
            count_d <= i
    {
        let c = a[i];
        if c == 'b' {
            count_b += 1;
        } else if c == 'a' {
            count_a += 1;
        } else if c == 'd' {
            count_d += 1;
        }
    }

    let mut result = Vec::new();
    for _ in 0..count_b {
        result.push('b');
    }
    for _ in 0..count_a {
        result.push('a');
    }
    for _ in 0..count_d {
        result.push('d');
    }

    proof {
        let b_seg = result@.subrange(0, count_b as int);
        let a_seg = result@.subrange(count_b as int, (count_b + count_a) as int);
        let d_seg = result@.subrange((count_b + count_a) as int, (count_b + count_a + count_d) as int);

        assert(forall|i: int| 0 <= i < b_seg.len() ==> b_seg[i] == 'b');
        assert(forall|i: int| 0 <= i < a_seg.len() ==> a_seg[i] == 'a');
        assert(forall|i: int| 0 <= i < d_seg.len() ==> d_seg[i] == 'd');

        lemma_concatenated_is_sortedbad(b_seg, a_seg, d_seg);

        assert(a@.count('b') == count_b);
        assert(a@.count('a') == count_a);
        assert(a@.count('d') == count_d);
        assert(result@.count('b') == count_b);
        assert(result@.count('a') == count_a);
        assert(result@.count('d') == count_d);

        let a_multiset = a@.to_multiset();
        let result_multiset = result@.to_multiset();
        assert(a_multiset.count('b') == result_multiset.count('b'));
        assert(a_multiset.count('a') == result_multiset
// </vc-code>

fn main() {}

}