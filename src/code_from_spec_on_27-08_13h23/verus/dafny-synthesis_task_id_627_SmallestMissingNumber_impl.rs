use vstd::prelude::*;

verus! {

// <vc-helpers>
proof fn lemma_seq_contains_up_to_n(s: Seq<i32>, n: i32)
    requires
        forall|i: int| 0 <= i < s.len() ==> 0 <= s[i] <= n,
        forall|i: int, j: int| 0 <= i < j < s.len() ==> s[i] <= s[j],
        s.len() > 0,
    ensures
        exists|k: i32| 0 <= k <= n && !s.contains(k),
{
    let mut i: i32 = 0;
    while i <= n
        invariant
            0 <= i <= n + 1,
            forall|k: i32| 0 <= k < i ==> s.contains(k),
    {
        if !s.contains(i) {
            return;
        }
        i = i + 1;
    }
}
// </vc-helpers>

// <vc-spec>
// <vc-spec>
spec fn smallest_missing_number(s: Seq<int>) -> int
    recommends
        forall|i: int, j: int| 0 <= i < j < s.len() ==> s[i] <= s[j],
        forall|i: int| 0 <= i < s.len() ==> s[i] >= 0,
{
// </vc-spec>
// </vc-spec>

// <vc-code>
fn find_smallest_missing_number(s: Vec<i32>) -> (result: i32)
    requires
        forall|i: int, j: int| 0 <= i < j < s.len() ==> s@[i] <= s@[j],
        forall|i: int| 0 <= i < s.len() ==> s@[i] >= 0,
    ensures
        result >= 0,
        !s@.contains(result),
        forall|k: i32| 0 <= k < result ==> s@.contains(k),
{
    let mut i: usize = 0;
    while i < s.len()
        invariant
            0 <= i <= s.len(),
            forall|k: i32| 0 <= k < i as i32 ==> s@.contains(k),
    {
        if s@[i] > i as i32 {
            return i as i32;
        }
        i = i + 1;
    }
    i as i32
}
// </vc-code>

}

fn main() {}

}