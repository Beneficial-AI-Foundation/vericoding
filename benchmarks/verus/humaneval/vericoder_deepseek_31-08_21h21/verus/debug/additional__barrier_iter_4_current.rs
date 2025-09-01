use vstd::prelude::*;

verus! {

// <vc-helpers>
proof fn lemma_seq_sorted_left<E: std::cmp::PartialOrd + vstd::prelude::SpecOrd>(s: Seq<E>, p: int) 
    requires
        0 <= p < s.len(),
        forall|k: int, l: int| 0 <= k <= p && p < l < s.len() ==> s[k].spec_lt(s[l]),
    ensures
        forall|i: int| 0 <= i <= p ==> s[i].spec_le(s[p]),
{
    assert forall|i: int| 0 <= i <= p implies s[i].spec_le(s[p]) by {
        if i != p {
            assert(s[i].spec_lt(s[p]));
        }
    };
}

proof fn lemma_seq_sorted_right<E: std::cmp::PartialOrd + vstd::prelude::SpecOrd>(s: Seq<E>, p: int) 
    requires
        0 <= p < s.len(),
        forall|k: int, l: int| 0 <= k <= p && p < l < s.len() ==> s[k].spec_lt(s[l]),
    ensures
        forall|j: int| p < j < s.len() ==> s[p].spec_lt(s[j]),
{
    assert forall|j: int| p < j < s.len() implies s[p].spec_lt(s[j]) by {
        assert(s[p].spec_lt(s[j]));
    };
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
            0 <= i <= p + 1,
            i <= n,
            forall|k: int| 0 <= k < i as int ==> arr_view[k] <= max_left,
            max_left == (if i > 0 { arr_view[(i-1) as int] } else { -2147483648i32 }),
        decreases (p - i)
    {
        if i < arr.len() {
            if arr[i] > max_left {
                max_left = arr[i];
            }
        }
        if i < p { i = i + 1; } else { i = p + 1; }
    }
    let mut min_right: i32 = 2147483647i32;
    let mut j: usize = p + 1;
    while j <= arr.len()
        invariant
            p < j <= arr.len(),
            forall|l: int| j as int <= l < n as int ==> arr_view[l] >= min_right,
            min_right == (if j < arr.len() { arr_view[j as int] } else { 2147483647i32 }),
        decreases (arr.len() - j)
    {
        if j < arr.len() {
            if arr[j] < min_right {
                min_right = arr[j];
            }
        }
        j = j + 1;
    }
    proof {
        lemma_seq_sorted_left(arr_view, p as int);
        lemma_seq_sorted_right(arr_view, p as int);
        if max_left <= min_right {
            assert forall|k: int, l: int| 0 <= k <= p as int && (p as int) < l < n as int implies arr_view[k] < arr_view[l] by {
                assert(arr_view[k] <= max_left);
                assert(min_right <= arr_view[l]);
            };
        }
    }
    max_left <= min_right
}
// </vc-code>

fn main() {}
}