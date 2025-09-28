// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Prove length preservation of string_swapcase by unfolding its recursive definition */
proof fn lemma_string_swapcase_len(s: Seq<char>)
    ensures
        string_swapcase(s).len() == s.len(),
    decreases s.len()
{
    if s.len() == 0 {
        assert(string_swapcase(s) == Seq::<char>::empty());
        assert(string_swapcase(s).len() == 0);
        assert(s.len() == 0);
    } else {
        lemma_string_swapcase_len(s.skip(1));
        assert(s.len() > 0);
        assert(string_swapcase(s) == seq![char_swapcase(s[0])] + string_swapcase(s.skip(1)));
        assert((seq![char_swapcase(s[0])] + string_swapcase(s.skip(1))).len() == 1 + string_swapcase(s.skip(1)).len());
        assert(s.skip(1).len() == s.len() - 1);
        assert(string_swapcase(s).len() == 1 + string_swapcase(s.skip(1)).len());
        assert(string_swapcase(s).len() == 1 + (s.len() - 1));
        assert(string_swapcase(s).len() == s.len());
    }
}

/* helper modified by LLM (iteration 5): Prove pointwise character transformation for string_swapcase */
proof fn lemma_string_swapcase_pointwise(s: Seq<char>)
    ensures
        forall|j: int| 0 <= j < s.len() ==> string_swapcase(s)[j] == char_swapcase(s[j]),
    decreases s.len()
{
    if s.len() == 0 {
    } else {
        lemma_string_swapcase_pointwise(s.skip(1));
        lemma_string_swapcase_len(s.skip(1));
        assert(forall|j: int| 0 <= j < s.len() ==> string_swapcase(s)[j] == char_swapcase(s[j])) by {
            let j: int = arbitrary();
            if 0 <= j && j < s.len() {
                assert(string_swapcase(s) == seq![char_swapcase(s[0])] + string_swapcase(s.skip(1)));
                if j == 0 {
                    assert(string_swapcase(s)[0] == char_swapcase(s[0]));
                } else {
                    assert(j > 0);
                    assert(seq![char_swapcase(s[0])].len() == 1);
                    assert(s.skip(1).len() == s.len() - 1);
                    assert(j - 1 < s.skip(1).len());
                    assert(string_swapcase(s.skip(1)).len() == s.skip(1).len());
                    assert(j - 1 < string_swapcase(s.skip(1)).len());
                    assert(string_swapcase(s)[j] == string_swapcase(s.skip(1))[j - 1]);
                    assert(s[j] == s.skip(1)[j - 1]);
                    assert(string_swapcase(s.skip(1))[j - 1] == char_swapcase(s.skip(1)[j - 1]));
                    assert(string_swapcase(s)[j] == char_swapcase(s[j]));
                }
            }
        }
    }
}

/* helper modified by LLM (iteration 5): Seq push preserves prior indices */
proof fn lemma_seq_push_index_preserved<A>(s: Seq<A>, x: A, k: int)
    requires
        0 <= k < s.len() as int,
    ensures
        (s.push(x))[k] == s[k],
{
    assert(s.push(x) == s + seq![x]);
    assert((s + seq![x])[k] == s[k]);
}

/* helper modified by LLM (iteration 5): Seq push yields new element at old length */
proof fn lemma_seq_push_last<A>(s: Seq<A>, x: A)
    ensures
        (s.push(x))[s.len() as int] == x,
{
    assert(s.push(x) == s + seq![x]);
    assert((s + seq![x]).len() == s.len() + 1);
    assert((s + seq![x])[s.len() as int] == x);
}
// </vc-helpers>

// <vc-spec>
spec fn char_swapcase(c: char) -> char;

spec fn string_swapcase(s: Seq<char>) -> Seq<char>
    decreases s.len()
{
    if s.len() == 0 {
        Seq::<char>::empty()
    } else {
        seq![char_swapcase(s[0])] + string_swapcase(s.skip(1))
    }
}

fn swapcase(a: Vec<String>) -> (result: Vec<String>)
    ensures
        result.len() == a.len(),
        forall|i: int| 0 <= i < a.len() ==> result[i]@.len() == a[i]@.len(),
        forall|i: int, j: int| 0 <= i < a.len() && 0 <= j < a[i]@.len() ==> 
            #[trigger] result[i]@[j] == char_swapcase(a[i]@[j])
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): use String::from_seq and maintain invariants */
    let n = a.len();
    let mut res: Vec<String> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            res.len() == i,
            i <= a.len(),
            forall|k: int| 0 <= k < i as int ==> res[k]@.len() == a[k]@.len(),
            forall|k: int, j: int|
                0 <= k < i as int && 0 <= j < a[k]@.len() ==> #[trigger] res[k]@[j] == char_swapcase(a[k]@[j]),
        decreases (n - i) as int
    {
        let ghost s_view = a@[i as int]@;
        let out: String = String::from_seq(string_swapcase(s_view));
        let len_before: usize = res.len();
        proof { assert(len_before == i); }
        let ghost prev = res@;
        proof {
            assert(prev == res@);
            assert(forall|k: int| 0 <= k < i as int ==> prev[k]@.len() == a[k]@.len()) by {
                let k: int = arbitrary();
                if 0 <= k && k < i as int {
                    assert(res@[k]@.len() == a[k]@.len());
                    assert(prev == res@);
                }
            }
            assert(forall|k: int, j: int|
                0 <= k < i as int && 0 <= j < a[k]@.len() ==> prev[k]@[j] == char_swapcase(a[k]@[j])) by {
                let k: int = arbitrary();
                let j: int = arbitrary();
                if 0 <= k && k < i as int && 0 <= j && j < a[k]@.len() {
                    assert(res@[k]@[j] == char_swapcase(a[k]@[j]));
                    assert(prev == res@);
                }
            }
            lemma_string_swapcase_len(s_view);
            lemma_string_swapcase_pointwise(s_view);
            assert(prev.len() == len_before as int);
        }
        res.push(out);
        proof {
            assert(len_before == i);
            assert(prev.len() == len_before as int);
            assert(res@ == prev.push(out));
            assert(forall|k: int| 0 <= k < i as int ==> res@[k] == prev[k]) by {
                let k: int = arbitrary();
                if 0 <= k && k < i as int {
                    lemma_seq_push_index_preserved(prev, out, k);
                    assert(res@ == prev.push(out));
                }
            }
            assert(forall|k: int| 0 <= k < i as int ==> res@[k]@.len() == a[k]@.len()) by {
                let k: int = arbitrary();
                if 0 <= k && k < i as int {
                    assert(res@[k] == prev[k]);
                    assert(prev[k]@.len() == a[k]@.len());
                }
            }
            assert(forall|k: int, j: int|
                0 <= k < i as int && 0 <= j < a[k]@.len() ==> res@[k]@[j] == char_swapcase(a[k]@[j])) by {
                let k: int = arbitrary();
                let j: int = arbitrary();
                if 0 <= k && k < i as int && 0 <= j && j < a[k]@.len() {
                    assert(res@[k] == prev[k]);
                    assert(prev[k]@[j] == char_swapcase(a[k]@[j]));
                }
            }
            lemma_seq_push_last(prev, out);
            let k_new = i as int;
            assert(prev.len() == k_new);
            assert((res@)[k_new] == out);
            assert((res@)[k_new]@.len() == a[k_new]@.len()) by {
                assert(out@ == string_swapcase(s_view));
                assert(string_swapcase(s_view).len() == s_view.len());
                assert(out@.len() == s_view.len());
                assert(s_view == a@[k_new]@);
            }
            assert(forall|j: int| 0 <= j < a[k_new]@.len() ==> (res@)[k_new]@[j] == char_swapcase(a[k_new]@[j])) by {
                let j: int = arbitrary();
                if 0 <= j && j < a[k_new]@.len() {
                    assert(out@ == string_swapcase(s_view));
                    assert(s_view == a@[k_new]@);
                    assert(string_swapcase(s_view)[j] == char_swapcase(s_view[j]));
                }
            }
        }
        i = i + 1;
    }
    res
}
// </vc-code>

}
fn main() {}