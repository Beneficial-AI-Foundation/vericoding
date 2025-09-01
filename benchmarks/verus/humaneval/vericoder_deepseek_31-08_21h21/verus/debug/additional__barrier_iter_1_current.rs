use vstd::prelude::*;

verus! {

// <vc-helpers>
proof fn lemma_seq_sorted_left<E: std::cmp::PartialOrd>(s: Seq<E>, p: usize) 
    requires
        0 <= p < s.len(),
        forall|k: int, l: int| 0 <= k <= p && p < l < s.len() ==> s[k] < s[l],
    ensures
        forall|i: int| 0 <= i <= p ==> s[i] <= s[p],
{
    assert forall|i: int| 0 <= i <= p implies s[i] <= s[p] by {
        assert(s[i] < s[p] || i == p);
        if i != p {
            assert(s[i] < s[p]);
        }
    };
}

proof fn lemma_seq_sorted_right<E: std::cmp::PartialOrd>(s: Seq<E>, p: usize) 
    requires
        0 <= p < s.len(),
        forall|k: int, l: int| 0 <= k <= p && p < l < s.len() ==> s[k] < s[l],
    ensures
        forall|j: int| p < j < s.len() ==> s[p] < s[j],
{
}
// </vc-helpers>

// <vc-spec>
#[verifier::loop_isolation(false)]
fn barrier(arr: &[i32], p: usize) -> (result: bool)
    // pre-conditions-start
    requires
        arr.len() > 0,
        0 <= p < arr.len(),
    // pre-conditions-end
    // post-conditions-start
    ensures
        result == forall|k: int, l: int| 0 <= k <= p && p < l < arr.len() ==> arr[k] < arr[l],
    // post-conditions-end
// </vc-spec>
// <vc-code>
{
    let arr_view = arr.view();
    let n = arr.len();
    let mut max_left: i32 = -2147483648i32;
    let mut i: usize = 0;
    while i <= p
        invariant
            0 <= i <= p as usize + 1,
            i <= n,
            forall|k: int| 0 <= k < i ==> arr_view[k] <= max_left,
            max_left == (if i > 0 { arr_view[i-1] as i32 } else { -2147483648i32 }) || i == 0,
        decreases (p - i)
    {
        if i < n {
            if arr[i] > max_left {
                max_left = arr[i];
            }
        }
        if i < p { i = i + 1; } else { i = p + 1; }
    }
    let mut min_right: i32 = 2147483647i32;
    let mut j: usize = p + 1;
    while j < n
        invariant
            p < j <= n,
            forall|l: int| j <= l < n ==> arr_view[l] >= min_right,
            min_right == (if j < n { arr_view[j] as i32 } else { 2147483647i32 }) || j == n,
        decreases (n - j)
    {
        if arr[j] < min_right {
            min_right = arr[j];
        }
        j = j + 1;
    }
    proof {
        lemma_seq_sorted_left(arr_view, p);
        lemma_seq_sorted_right(arr_view, p);
        if max_left <= min_right {
            assert forall|k: int, l: int| 0 <= k <= p && p < l < n implies arr_view[k] < arr_view[l] by {
                assert(arr_view[k] <= max_left);
                assert(min_right <= arr_view[l]);
                assert(max_left <= min_right);
            };
        }
    }
    max_left <= min_right
}
// </vc-code>

fn main() {}
}