use vstd::prelude::*;

verus! {

// <vc-helpers>
// </vc-helpers>
// </vc-helpers>

// <vc-spec>
fn replace(v: &mut Vec<i32>, x: i32, y: i32)
    ensures
        forall|k: int| 0 <= k < old(v).len() && old(v)[k] == x ==> v[k] == y,
        forall|k: int| 0 <= k < old(v).len() && old(v)[k] != x ==> v[k] == old(v)[k],
// </vc-spec>
// <vc-code>
{
    let n = v.len();
    proof {
        assert(n == old(v).len());
    }
    let mut i: usize = 0;
    while i < n
        invariant
            v.len() == n,
            i <= n,
            forall|k: int|
                0 <= k && k < i as int ==> #[trigger] v@[k] == if old(v)@[k] == x { y } else { old(v)@[k] },
            forall|k: int|
                i as int <= k && k < n as int ==> #[trigger] v@[k] == old(v)@[k],
        decreases (n - i) as int
    {
        assert(i < v.len());
        let cur = v[i];
        if cur == x {
            proof {
                assert(v@[i as int] == old(v)@[i as int]);
                assert(cur == v@[i as int]);
                assert(old(v)@[i as int] == x);
            }
            v.set(i, y);
        } else {
            proof {
                assert(v@[i as int] == old(v)@[i as int]);
                assert(cur == v@[i as int]);
                assert(old(v)@[i as int] != x);
            }
        }
        i = i + 1;
    }
    proof {
        assert(i == n);
        assert(forall|k: int| 0 <= k && k < n ==> #[trigger] v@[k] == if old(v)@[k] == x { y } else { old(v)@[k] }) by {
            assert(i == n);
        }
    }
}
// </vc-code>

fn main() {
}

}