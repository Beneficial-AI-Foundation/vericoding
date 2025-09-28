use vstd::prelude::*;

verus! {

/**
 * Filter odd numbers from an array of numbers
 **/

spec fn is_odd(n: int) -> bool {
    n % 2 != 0
}

// <vc-helpers>
proof fn lemma_contains_of_seq_push<T>(s: Seq<T>, x: T)
    ensures s.push(x).contains(x)
{
    assert(s.push(x).contains(x)) by {
        let j = s.len();
        assert(0 <= j && j < s.push(x).len());
        assert(s.push(x)[j] == x);
    }
}

proof fn lemma_index_of_seq_push_preserves<T>(s: Seq<T>, x: T, j: int)
    requires
        0 <= j && j < s.len(),
    ensures
        s.push(x)[j] == s[j],
        s.push(x).len() == s.len() + 1,
{
    assert(s.push(x).len() == s.len() + 1);
    assert(0 <= j && j < s.push(x).len());
    assert(s.push(x)[j] == s[j]);
}

proof fn lemma_contains_preserved_on_push<T>(s: Seq<T>, y: T, x: T)
    requires s.contains(x)
    ensures s.push(y).contains(x)
{
    let j = choose|j: int| 0 <= j && j < s.len() && s[j] == x;
    assert(0 <= j && j < s.len());
    lemma_index_of_seq_push_preserves(s, y, j);
    assert(0 <= j && j < s.push(y).len());
    assert(s.push(y)[j] == x);
}

proof fn lemma_contains_at_index<T>(s: Seq<T>, j: int)
    requires 0 <= j && j < s.len()
    ensures s.contains(s[j])
{
    assert(s.contains(s[j])) by {
        let idx = j;
        assert(0 <= idx && idx < s.len());
        assert(s[idx] == s[j]);
    }
}

proof fn lemma_index_of_seq_push_new<T>(s: Seq<T>, x: T)
    ensures
        s.push(x)[s.len()] == x,
        s.push(x).len() == s.len() + 1,
{
    assert(s.push(x).len() == s.len() + 1);
    let j = s.len();
    assert(0 <= j && j < s.push(x).len());
    assert(s.push(x)[j] == x);
}
// </vc-helpers>

// <vc-spec>
fn filter_odd_numbers(arr: &[int]) -> (odd_list: Vec<int>)
    ensures 
        // All numbers in the output are odd and exist in the input 
        forall|i: int| 0 <= i < odd_list.len() ==> is_odd(odd_list[i]) && arr@.contains(odd_list[i]),
        // All odd numbers in the input are in the output
        forall|i: int| 0 <= i < arr.len() && is_odd(arr[i]) ==> odd_list@.contains(arr[i]),
// </vc-spec>
// <vc-code>
{
    let mut v: Vec<int> = Vec::new();
    let mut i: usize = 0;
    while i < arr.len()
        invariant i <= arr.len()
        invariant forall|k: int| 0 <= k && k < v.len() as int ==> is_odd(v@[k]) && arr@.contains(v@[k])
        invariant forall|j: int| 0 <= j && j < i as int && is_odd(arr@[j]) ==> v@.contains(arr@[j])
        decreases (arr.len() - i) as int
    {
        let a = arr[i];
        if is_odd(a) {
            let old_seq = v@;
            let old_len = old_seq.len();
            proof {
                assert(old_seq == v@);
                assert forall|k: int| 0 <= k && k < old_len ==> is_odd(old_seq[k]) && arr@.contains(old_seq[k]) by {
                    assert(0 <= k && k < v.len() as int);
                };
                assert forall|j: int| 0 <= j && j < i as int && is_odd(arr@[j]) ==> old_seq.contains(arr@[j]) by {
                    assert(old_seq == v@);
                };
            }
            v.push(a);
            assert(v@ == old_seq.push(a));
            proof {
                assert(v@.len() == old_len + 1);
                assert forall|k: int| 0 <= k && k < v.len() as int ==> is_odd(v@[k]) && arr@.contains(v@[k]) by {
                    if k < old_len {
                        assert(v@[k] == old_seq.push(a)[k]);
                        lemma_index_of_seq_push_preserves(old_seq, a, k);
                        assert(old_seq.push(a)[k] == old_seq[k]);
                        assert(is_odd(old_seq[k]) && arr@.contains(old_seq[k]));
                    } else {
                        assert(v@.len() == old_len + 1);
                        assert(k == old_len);
                        assert(v@[k] == old_seq.push(a)[k]);
                        lemma_index_of_seq_push_new(old_seq, a);
                        assert(old_seq.push(a)[k] == a);
                        assert(is_odd(a));
                        lemma_contains_at_index(arr@, i as int);
                        assert(arr@.contains(arr@[i as int]));
                        assert(arr@[i as int] == a);
                    }
                };
            }
            proof {
                assert forall|j: int| 0 <= j && j < (i as int + 1) && is_odd(arr@[j]) ==> v@.contains(arr@[j]) by {
                    if j < i as int {
                        assert(old_seq.contains(arr@[j]));
                        lemma_contains_preserved_on_push(old_seq, a, arr@[j]);
                        assert(v@ == old_seq.push(a));
                        assert(v@.contains(arr@[j]));
                    } else {
                        assert(j == i as int);
                        assert(arr@[j] == a);
                        lemma_contains_of_seq_push(old_seq, a);
                        assert(v@ == old_seq.push(a));
                        assert(v@.contains(arr@[j]));
                    }
                };
            }
            i = i + 1;
        } else {
            i = i + 1;
        }
    }
    v
}
// </vc-code>

fn main() {}

}