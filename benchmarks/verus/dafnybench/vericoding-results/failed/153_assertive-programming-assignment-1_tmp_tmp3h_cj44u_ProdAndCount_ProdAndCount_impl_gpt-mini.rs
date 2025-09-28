use vstd::prelude::*;

verus! {

spec fn recursive_positive_product(q: Seq<int>) -> int
    decreases q.len()
{
    if q.len() == 0 {
        1
    } else if q[0] <= 0 {
        recursive_positive_product(q.subrange(1, q.len() as int))
    } else {
        q[0] * recursive_positive_product(q.subrange(1, q.len() as int))
    }
}

spec fn recursive_count(key: int, q: Seq<int>) -> int
    decreases q.len()
{
    if q.len() == 0 {
        0
    } else if q[q.len() - 1] == key {
        1 + recursive_count(key, q.subrange(0, q.len() as int - 1))
    } else {
        recursive_count(key, q.subrange(0, q.len() as int - 1))
    }
}

spec fn county(elem: int, key: int) -> int {
    if elem == key { 1 } else { 0 }
}

spec fn prody(elem: int) -> int {
    if elem <= 0 { 1 } else { elem }
}

// <vc-helpers>
// <vc-helpers>
// No additional helpers required for this proof.
// </vc-helpers>
// </vc-helpers>

// <vc-spec>
fn prod_and_count(q: &[i32], key: i32) -> (i32, u32)
    ensures |result: (i32, u32)| 
        result.0 == recursive_positive_product(q@.map(|_, x: i32| x as int)) &&
        result.1 == recursive_count(key as int, q@.map(|_, x: i32| x as int)) as u32
// </vc-spec>
// <vc-code>
{
    let s = q@.map(|_, x: i32| x as int);
    let n: nat = s.len();
    let key_i: int = key as int;

    let mut i: nat = n;
    let mut prod: int = 1;
    let mut cnt: int = 0;

    while i > 0
        invariant i <= n
        invariant prod == recursive_positive_product(s.subrange(i as int, n as int))
        invariant cnt == recursive_count(key_i, s.subrange(i as int, n as int))
        decreases i
    {
        let old_i = i;
        let old_prod = prod;
        let old_cnt = cnt;

        let elem: int = s@[((old_i as int) - 1)];

        if elem <= 0 {
            prod = prod;
        } else {
            prod = elem * prod;
        }

        if elem == key_i {
            cnt = cnt + 1;
        }

        i = old_i - 1;

        proof {
            assert(old_i > 0);

            // Invariant at loop start for prod and cnt
            assert(old_prod == recursive_positive_product(s.subrange(old_i as int, n as int)));
            assert(old_cnt == recursive_count(key_i, s.subrange(old_i as int, n as int)));

            // Relate the new suffix s.subrange(i, n) to old suffix
            assert(s.subrange(i as int, n as int) == s.subrange(old_i as int - 1, n as int));
            // The head of the new suffix is elem
            assert(s.subrange(i as int, n as int)@[0] == elem);
            // The tail of the new suffix is the old suffix
            assert(s.subrange((i as int) + 1, n as int) == s.subrange(old_i as int, n as int));

            // Unfold recursive_positive_product for non-empty suffix
            assert(
                recursive_positive_product(s.subrange(i as int, n as int)) ==
                if s.subrange(i as int, n as int)@[0] <= 0 {
                    recursive_positive_product(s.subrange((i as int) + 1, n as int))
                } else {
                    s.subrange(i as int, n as int)@[0] * recursive_positive_product(s.subrange((i as int) + 1, n as int))
                }
            );

            if elem <= 0 {
                assert(recursive_positive_product(s.subrange(i as int, n as int)) == old_prod);
                assert(prod == old_prod);
                assert(prod == recursive_positive_product(s.subrange(i as int, n as int)));
            } else {
                assert(recursive_positive_product(s.subrange(i as int, n as int)) == elem * old_prod);
                assert(prod == elem * old_prod);
                assert(prod == recursive_positive_product(s.subrange(i as int, n as int)));
            }

            // Unfold recursive_count for non-empty suffix
            assert(
                recursive_count(key_i, s.subrange(i as int, n as int)) ==
                if s.subrange(i as int, n as int)@[0] == key_i {
                    1 + recursive_count(key_i, s.subrange((i as int) + 1, n as int))
                } else {
                    recursive_count(key_i, s.subrange((i as int) + 1, n as int))
                }
            );

            if elem == key_i {
                assert(recursive_count(key_i, s.subrange(i as int, n as int)) == 1 + old_cnt);
                assert(cnt == 1 + old_cnt);
                assert(cnt == recursive_count(key_i, s.subrange(i as int, n as int)));
            } else {
                assert(recursive_count(key_i, s.subrange(i as int, n as int)) == old_cnt);
                assert(cnt == old_cnt);
                assert(cnt == recursive_count(key_i, s.subrange(i as int, n as int)));
            }
        }
    }

    (prod as i32, cnt as u32)
}
// </vc-code>

fn main() {}

}