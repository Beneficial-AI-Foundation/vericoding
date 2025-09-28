use vstd::prelude::*;

verus! {

// <vc-helpers>

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
    if a.len() <= 1 {
        (a, Vec::new())
    } else {
        let mid = a.len() / 2;
        let mut left = Vec::new();
        let mut right = Vec::new();
        
        let mut i = 0;
        while i < mid
            invariant
                i <= mid,
                mid <= a.len(),
                left.len() == i,
                right.len() == 0,
                forall|j: int| 0 <= j < i ==> left@[j] == a@[j],
            decreases mid - i,
        {
            left.push(a[i]);
            i += 1;
        }
        
        while i < a.len()
            invariant
                mid <= i <= a.len(),
                left.len() == mid,
                right.len() == i - mid,
                forall|j: int| 0 <= j < mid ==> left@[j] == a@[j],
                forall|j: int| 0 <= j < i - mid ==> right@[j] == a@[mid + j],
            decreases a.len() - i,
        {
            right.push(a[i]);
            i += 1;
        }
        
        proof {
            assert(left@ + right@ =~= a@);
            assert(left.len() + right.len() == a.len());
            assert(left.len() == mid);
            assert(right.len() == a.len() - mid);
            assert(mid < a.len());
            assert(a.len() - mid < a.len());
        }
        
        (left, right)
    }
}
// </vc-code>

fn main() {
}

}