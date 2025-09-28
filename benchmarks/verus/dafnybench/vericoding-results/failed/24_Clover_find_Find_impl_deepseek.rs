use vstd::prelude::*;

verus! {

// <vc-helpers>
proof fn lemma_seq_subrange_index_property<K>(s: Seq<K>, i: int, j: int, k: int)
    requires
        0 <= i <= k < j <= s.len(),
    ensures
        s[k] == s.subrange(i, j)[k - i],
{
}

proof fn lemma_index_in_bounds<K>(s: Seq<K>, i: int)
    requires
        0 <= i < s.len(),
    ensures
        s[i] == s[i],
{
}

proof fn lemma_forall_implies_positive<K>(s: Seq<K>, start: int, end: int, key: K)
    requires
        0 <= start <= end <= s.len(),
        forall|i: int| start <= i < end ==> s[i] != key,
    ensures
        forall|i: int| 0 <= i < end ==> (i < start || s[i] != key),
{
    assert forall|i: int| 0 <= i < end implies (i < start || s[i] != key) by {
        if i >= start {
            assert(s[i] != key);
        }
    };
}

proof fn lemma_seq_to_slice_index_equality(a: &[i32], i: int)
    requires
        0 <= i < a.len() as int,
    ensures
        a[i] == a@[i],
{
}

proof fn lemma_preserves_forall_negative<K>(s: Seq<K>, start: int, end: int, key: K, j: int)
    requires
        0 <= start <= end <= s.len(),
        j == end as int,
        forall|i: int| start <= i < end ==> s[i] != key,
        s[j] != key,
    ensures
        forall|i: int| start <= i < end + 1 ==> s[i] != key,
{
    assert forall|i: int| start <= i < end + 1 implies s[i] != key by {
        if i < end {
            assert(s[i] != key);
        } else {
            assert(i == end);
            assert(s[i] != key);
        }
    };
}
// </vc-helpers>

// <vc-spec>
fn find(a: &[i32], key: i32) -> (index: i32)
    ensures
        -1 <= index < a.len() as i32,
        index != -1 ==> a[index as int] == key && (forall|i: int| 0 <= i < index ==> a[i] != key),
        index == -1 ==> (forall|i: int| 0 <= i < a.len() ==> a[i] != key),
// </vc-spec>
// <vc-code>
{
    let mut idx: i32 = -1;
    let mut j: usize = 0;
    
    while j < a.len()
        invariant
            j <= a.len(),
            idx == -1 ==> forall|i: int| 0 <= i < j as int ==> a[i] != key,
            idx != -1 ==> idx >= 0 && (idx as usize) < j && a[idx as usize] == key && forall|i: int| 0 <= i < idx ==> a[i] != key,
        decreases a.len() - j
    {
        if a[j] == key {
            idx = j as i32;
            break;
        }
        proof {
            lemma_preserves_forall_negative(a@, 0, j as int, key, j as int);
        }
        j = j + 1;
    }
    
    if idx == -1 {
        proof {
            lemma_forall_implies_positive(a@, 0, a.len() as int, key);
            assert forall|i: int| 0 <= i < a.len() implies a[i] != key by {
                if i < a.len() as int {
                    assert(a[i] != key);
                }
            };
        }
    } else {
        proof {
            assert(0 <= idx && (idx as usize) < a.len());
            assert(a[idx as usize] == key);
            assert forall|i: int| 0 <= i < idx implies a[i] != key by {
                if i < idx {
                    assert(a[i] != key);
                }
            };
        }
    }
    
    idx
}
// </vc-code>

fn main() {}

}