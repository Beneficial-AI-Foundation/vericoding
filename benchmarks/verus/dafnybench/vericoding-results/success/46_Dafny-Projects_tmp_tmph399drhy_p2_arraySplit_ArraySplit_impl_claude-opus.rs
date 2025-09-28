use vstd::prelude::*;

verus! {

// <vc-helpers>
// No additional helpers needed
// </vc-helpers>

// <vc-spec>
fn array_split(a: Vec<i32>) -> (ret: (Vec<i32>, Vec<i32>))
    ensures
        a@ == ret.0@ + ret.1@,
        a.len() == ret.0.len() + ret.1.len(),
        a.len() > 1 ==> a.len() > ret.0.len(),
        a.len() > 1 ==> a.len() > ret.1.len(),
// </vc-spec>
// <vc-code>
{
    let n = a.len();
    if n <= 1 {
        (a, Vec::new())
    } else {
        let mid = n / 2;
        let mut left = Vec::new();
        let mut right = Vec::new();
        
        let mut i: usize = 0;
        while i < n
            invariant
                0 <= i <= n,
                n == a.len(),
                mid == n / 2,
                i <= mid ==> left@.len() == i as nat,
                i > mid ==> left@.len() == mid as nat,
                i <= mid ==> right@.len() == 0,
                i > mid ==> right@.len() == (i - mid) as nat,
                forall|j: int| 0 <= j < left@.len() ==> #[trigger] left@[j] == a@[j],
                forall|j: int| 0 <= j < right@.len() ==> #[trigger] right@[j] == a@[mid as int + j],
            decreases n - i
        {
            if i < mid {
                assert(i < a.len()); // Help prove precondition
                left.push(a[i]);
            } else {
                assert(i < a.len()); // Help prove precondition
                right.push(a[i]);
            }
            i = i + 1;
        }
        
        assert(left@.len() == mid as nat);
        assert(right@.len() == (n - mid) as nat);
        assert(left@ + right@ =~= a@) by {
            assert forall|k: int| 0 <= k < a@.len() implies #[trigger] ((left@ + right@)[k]) == a@[k] by {
                if k < mid {
                    assert((left@ + right@)[k] == left@[k]);
                    assert(left@[k] == a@[k]);
                } else {
                    assert((left@ + right@)[k] == right@[k - mid]);
                    assert(right@[k - mid] == a@[k]);
                }
            }
        }
        
        (left, right)
    }
}
// </vc-code>

fn main() {
}

}