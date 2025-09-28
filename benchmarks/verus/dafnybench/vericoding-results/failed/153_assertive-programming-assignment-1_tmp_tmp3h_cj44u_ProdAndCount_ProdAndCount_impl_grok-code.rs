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
spec fn as_ints(q: Seq<i32>) -> Seq<int> {
    q.map(|_, x: i32| x as int)
}
// </vc-helpers>

// <vc-spec>
fn prod_and_count(q: &[i32], key: i32) -> (i32, u32)
    ensures |result: (i32, u32)| 
        result.0 == recursive_positive_product(q@.map(|_, x: i32| x as int)) &&
        result.1 == recursive_count(key as int, q@.map(|_, x: i32| x as int)) as u32
// </vc-spec>
// <vc-code>
{
    let mut prod: i32 = 1;
    let mut count: u32 = 0;
    let mut i: nat = 0;
    while i < q@.len()
        invariant
            i <= q@.len(),
            prod == recursive_positive_product(as_ints(q@.subrange(0, i as int))),
            count == recursive_count(key as int, as_ints(q@.subrange(0, i as int))) as u32,
        decreases q@.len() - i
    {
        let elem = q@[i];
        if elem > 0 {
            prod = prod.checked_mul(elem).expect("overflow");
            proof {
                assert(recursive_positive_product(as_ints(q@.subrange(0, i as int))) * (elem as int) ==
                       recursive_positive_product(as_ints(q@.subrange(0, (i + 1) as int))));
            };
        } else {
            proof {
                assert(recursive_positive_product(as_ints(q@.subrange(0, i as int))) ==
                       recursive_positive_product(as_ints(q@.subrange(0, (i + 1) as int))));
            };
        }
        if elem == key {
            count = count + 1;
            proof {
                assert(recursive_count(key as int, as_ints(q@.subrange(0, (i + 1) as int))) ==
                       recursive_count(key as int, as_ints(q@.subrange(0, i as int))) + 1);
            };
        } else {
            proof {
                assert(recursive_count(key as int, as_ints(q@.subrange(0, (i + 1) as int))) ==
                       recursive_count(key as int, as_ints(q@.subrange(0, i as int))));
            };
        }
        i = i + 1;
    }
    (prod, count)
}
// </vc-code>

fn main() {}

}