// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

proof fn lemma_seq_split_at<T>(s: Seq<T>, mid: int)
    requires
        0 <= mid <= s.len(),
    ensures
        s =~= s.take(mid) + s.drop(mid)
{
}

proof fn lemma_seq_take_drop_len<T>(s: Seq<T>, n: int)
    requires
        0 <= n <= s.len(),
    ensures
        s.take(n).len() == n,
        s.drop(n).len() == s.len() - n
{
}

proof fn lemma_seq_permutation_reflexive<T>(s: Seq<T>)
    ensures
        s =~= s
{
}

proof fn lemma_seq_permutation_transitive<T>(s1: Seq<T>, s2: Seq<T>, s3: Seq<T>)
    requires
        s1 =~= s2,
        s2 =~= s3,
    ensures
        s1 =~= s3
{
}

proof fn lemma_sorted_concat(x: Vec<i32>, y: Vec<i32>)
    requires
        x.is_sorted(),
        y.is_sorted(),
        forall|i: int, j: int| 0 <= i < x.len() && 0 <= j < y.len() ==> x[i] <= y[j],
    ensures
        (x + y).is_sorted()
{
}

spec fn is_sorted_sequence(s: Seq<i32>) -> bool {
    forall|i: int, j: int| 0 <= i < j < s.len() ==> s[i] <= s[j]
}

spec fn seq_equals_vec(v: Vec<i32>) -> Seq<i32> {
    v@
}

// </vc-helpers>

// <vc-spec>
fn merge_sort(list: Vec<i32>) -> (result: Vec<i32>)
    ensures
        result.len() == list.len(),
        forall|i: int, j: int| 0 <= i < j < result.len() ==> result[i] <= result[j],
        result@ =~= list@,
// </vc-spec>
// <vc-code>
{
    if list.len() <= 1 {
        return list;
    }
    
    let mid = list.len() / 2;
    let left = merge_sort(list.take(mid));
    let right = merge_sort(list.drop(mid));
    
    let mut result = Vec::new();
    let mut i = 0;
    let mut j = 0;
    
    while i < left.len() && j < right.len() {
        if left[i] <= right[j] {
            result.push(left[i]);
            i += 1;
        } else {
            result.push(right[j]);
            j += 1;
        }
    }
    
    while i < left.len() {
        result.push(left[i]);
        i += 1;
    }
    
    while j < right.len() {
        result.push(right[j]);
        j += 1;
    }
    
    result
}
// </vc-code>

}
fn main() {}