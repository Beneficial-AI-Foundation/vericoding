use vstd::prelude::*;

verus! {

spec fn has_count(v: int, a: Seq<int>, n: nat) -> int
    decreases n
{
    if n == 0 {
        0
    } else {
        if a[n-1] == v {
            has_count(v, a, (n-1) as nat) + 1
        } else {
            has_count(v, a, (n-1) as nat)
        }
    }
}

// <vc-helpers>
proof fn lemma_has_count_zero(v: int, a: Seq<int>)
    ensures has_count(v, a, 0) == 0
{
    assert(has_count(v, a, 0) == 0);
}

proof fn lemma_has_count_step(v: int, a: Seq<int>, k: nat)
    ensures has_count(v, a, k + 1) == has_count(v, a, k) + (if a[k as int] == v { 1 } else { 0 })
{
    let n = k + 1;
    assert(n != 0);
    assert(n - 1 == k);

    assert(
        has_count(v, a, n)
        ==
        if n == 0 {
            0
        } else {
            if a[(n - 1) as int] == v {
                has_count(v, a, (n - 1) as nat) + 1
            } else {
                has_count(v, a, (n - 1) as nat)
            }
        }
    );

    assert(
        has_count(v, a, n)
        ==
        if a[k as int] == v {
            has_count(v, a, k) + 1
        } else {
            has_count(v, a, k)
        }
    );

    if a[k as int] == v {
        assert(has_count(v, a, n) == has_count(v, a, k) + 1);
        assert(has_count(v, a, n) == has_count(v, a, k) + (if a[k as int] == v { 1 } else { 0 }));
    } else {
        assert(has_count(v, a, n) == has_count(v, a, k));
        assert(has_count(v, a, n) == has_count(v, a, k) + (if a[k as int] == v { 1 } else { 0 }));
    }
}
// </vc-helpers>

// <vc-spec>
fn count(v: i32, a: &[i32], n: usize) -> (r: i32)
    requires n <= a.len()
    ensures n <= a.len() ==> has_count(v as int, a@.map_values(|x: i32| x as int), n as nat) == r as int
// </vc-spec>
// <vc-code>
{
    let mut r: i32 = 0;
    let mut i: usize = 0;

    proof {
        lemma_has_count_zero(v as int, a@.map_values(|x: i32| x as int));
        assert(a@.len() == a.len() as int);
    }

    while i < n
        invariant
            i <= n,
            i <= a.len(),
            r as int == has_count(v as int, a@.map_values(|x: i32| x as int), i as nat)
    {
        let old_i = i;
        let ai = a[old_i];

        if ai == v {
            r = r + 1;
        }

        proof {
            let a_int = a@.map_values(|x: i32| x as int);

            assert(old_i < a.len());
            assert(a@.len() == a.len() as int);
            assert((old_i as int) < (a@.len() as int));

            lemma_has_count_step(v as int, a_int, old_i as nat);

            assert(a@[old_i as int] == ai);
            assert(a_int[old_i as int] == (a@[old_i as int]) as int);

            if ai == v {
                assert(a_int[old_i as int] == v as int);
                assert(
                    has_count(v as int, a_int, (old_i + 1) as nat)
                    ==
                    has_count(v as int, a_int, old_i as nat) + 1
                );
            } else {
                // From a@[old_i] == ai and ai != v, we get a@[old_i] != v
                assert(a@[old_i as int] != v);
                // Casting preserves inequality
                assert((a@[old_i as int]) as int != v as int);
                assert(a_int[old_i as int] != v as int);
                assert(
                    has_count(v as int, a_int, (old_i + 1) as nat)
                    ==
                    has_count(v as int, a_int, old_i as nat)
                );
            }
        }

        i = i + 1;
    }

    proof {
        assert(i == n);
    }

    r
}
// </vc-code>

fn main() {
}

}