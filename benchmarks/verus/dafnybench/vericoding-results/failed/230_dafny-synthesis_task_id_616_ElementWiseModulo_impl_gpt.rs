use vstd::prelude::*;

verus! {

// <vc-helpers>
// no helpers needed
// </vc-helpers>

// <vc-spec>
fn element_wise_modulo(a: &[i32], b: &[i32]) -> (result: Vec<i32>)
    requires 
        a.len() == b.len(),
        forall|i: int| 0 <= i < b.len() ==> b[i] != 0,
    ensures 
        result.len() == a.len(),
        forall|i: int| 0 <= i < result.len() ==> result[i] == a[i] % b[i],
// </vc-spec>
// <vc-code>
{
    let n = a.len();
    let mut res: Vec<i32> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            n == a.len(),
            n == b.len(),
            i <= n,
            res.len() == i,
            forall|j: int|
                0 <= j < i as int ==>
                #[trigger] res@[j] == a[j] % b[j],
        decreases n - i
    {
        let ai = a[i];
        let bi = b[i];

        assert(0 <= i as int);
        assert((i as int) < (a.len() as int));
        assert((i as int) < (b.len() as int));

        assert(ai == a[i as int]);
        assert(bi == b[i as int]);

        // From the precondition: forall k. 0 <= k < b.len() ==> b[k] != 0
        // instantiate with k = i as int
        assert(b[i as int] != 0);
        assert(bi != 0);

        let val = ai % bi;
        res.push(val);
        proof {
            assert(res@[i as int] == val);
            assert(val == a[i as int] % b[i as int]);
        }
        i += 1;
    }
    res
}
// </vc-code>

fn main() {
}

}