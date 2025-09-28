use vstd::prelude::*;

verus! {

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn symmetric(a: &[i32]) -> (flag: bool)
    ensures 
        flag == true ==> forall|x: int| 0 <= x < a.len() ==> #[trigger] a[x] == a[a.len() - x - 1],
        flag == false ==> exists|x: int| #[trigger] a[x] != a[a.len() - x - 1] && 0 <= x < a.len(),
// </vc-spec>
// <vc-code>
{
    let n = a.len();
    for i in 0..n / 2
        invariant
            forall|x: int| 0 <= x < i ==> #[trigger] a@[x] == a@[n - x - 1],
    {
        assert(0 <= i < n / 2);
        assert(n - i - 1 < n);
        assert(0 <= n - i - 1);
        if a[i] != a[n - i - 1] {
            assert(exists|x: int| #[trigger] a@[x] != a@[n - x - 1] && 0 <= x < n) by {
                assert(0 <= i < n);
                assert(a@[i as int] != a@[n - i - 1]);
            }
            return false;
        }
    }
    
    proof {
        assert(forall|x: int| 0 <= x < n / 2 ==> #[trigger] a@[x] == a@[n - x - 1]);
        assert(forall|x: int| 0 <= x < n ==> #[trigger] a@[x] == a@[n - x - 1]) by {
            assert(forall|x: int| 0 <= x < n ==> #[trigger] a@[x] == a@[n - x - 1]) by {
                if n == 0 {
                    assert(forall|x: int| 0 <= x < n ==> #[trigger] a@[x] == a@[n - x - 1]);
                } else {
                    assert(forall|x: int| 0 <= x < n ==> #[trigger] a@[x] == a@[n - x - 1]) by {
                        forall|x: int| 0 <= x < n
                            ensures a@[x] == a@[n - x - 1]
                        {
                            if x < n / 2 {
                                assert(a@[x] == a@[n - x - 1]);
                            } else if x >= (n + 1) / 2 {
                                let y = n - x - 1;
                                assert(y < n / 2);
                                assert(a@[y] == a@[n - y - 1]);
                                assert((n - y - 1) == x);
                                assert(a@[x] == a@[n - x - 1]);
                            } else {
                                assert(x == n / 2);
                                assert((n - x - 1) == x);
                                assert(a@[x] == a@[n - x - 1]);
                            }
                        }
                    }
                }
            }
        }
    }
    
    true
}
// </vc-code>

fn main() {}

}