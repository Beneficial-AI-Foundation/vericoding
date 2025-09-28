use vstd::prelude::*;

verus! {

// <vc-helpers>
// no helpers needed
// </vc-helpers>

// <vc-spec>
fn linear_search(a: &[i32], e: i32) -> (n: usize)
    ensures 
        n <= a.len(),
        n == a.len() || a[n as int] == e,
        forall|i: int| 0 <= i < n ==> e != a[i],
// </vc-spec>
// <vc-code>
{
    let mut i: usize = 0;
    while i < a.len()
        invariant
            i <= a.len(),
            forall|j: int| 0 <= j < i as int ==> #[trigger] a[j] != e,
        decreases a.len() - i
    {
        let v_i = a[i];
        if v_i == e {
            assert(a[i as int] == v_i);
            return i;
        }
        assert(a[i as int] == v_i);
        assert(a[i as int] != e);
        proof {
            let i_old = i;
            assert_forall_by(|j: int| {
                requires(0 <= j && j < i_old as int + 1);
                ensures(a[j] != e);
                if j < i_old as int {
                    assert(forall|k: int| 0 <= k < i_old as int ==> #[trigger] a[k] != e);
                    assert(0 <= j && j < i_old as int);
                    assert(a[j] != e);
                } else {
                    assert(j <= i_old as int);
                    assert(!(j < i_old as int));
                    assert(j == i_old as int);
                    assert(i_old == i);
                    assert(j == i as int);
                    assert(a[j] == a[i as int]);
                    assert(a[i as int] != e);
                    assert(a[j] != e);
                }
            });
            assert(forall|j: int| 0 <= j && j < i_old as int + 1 ==> #[trigger] a[j] != e);
            assert(i + 1 <= a.len());
        }
        i += 1;
    }
    assert(!(i < a.len()));
    assert(i <= a.len());
    assert(i == a.len());
    i
}
// </vc-code>

fn main() {}

}