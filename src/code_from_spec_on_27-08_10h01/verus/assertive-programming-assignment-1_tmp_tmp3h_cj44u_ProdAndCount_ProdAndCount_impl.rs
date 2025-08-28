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
proof fn recursive_positive_product_fold_equiv(q: Seq<int>)
    ensures recursive_positive_product(q) == q.fold_left(1, |acc: int, elem: int| acc * prody(elem))
    decreases q.len()
{
    if q.len() == 0 {
    } else {
        recursive_positive_product_fold_equiv(q.subrange(1, q.len() as int));
        assert(q.drop_first() == q.subrange(1, q.len() as int));
    }
}

proof fn recursive_count_fold_equiv(key: int, q: Seq<int>)
    ensures recursive_count(key, q) == q.fold_right(|elem: int, acc: int| county(elem, key) + acc, 0int)
    decreases q.len()
{
    if q.len() == 0 {
    } else {
        recursive_count_fold_equiv(key, q.subrange(0, q.len() as int - 1));
        assert(q.drop_last() == q.subrange(0, q.len() as int - 1));
    }
}
// </vc-helpers>

// <vc-spec>
// <vc-spec>
fn prod_and_count(q: &[i32], key: i32) -> (i32, u32)
    ensures |result: (i32, u32)| 
        result.0 == recursive_positive_product(q@.map(|_, x: i32| x as int)) &&
        result.1 == recursive_count(key as int, q@.map(|_, x: i32| x as int)) as u32
// </vc-spec>
// </vc-spec>

// <vc-code>
{
    let mut product: i32 = 1;
    let mut count: u32 = 0;
    
    for i in 0..q.len()
        invariant
            product == q@.map(|_, x: i32| x as int).subrange(0, i as int).fold_left(1, |acc: int, elem: int| acc * prody(elem)),
            count as int == q@.map(|_, x: i32| x as int).subrange(0, i as int).fold_right(|elem: int, acc: int| county(elem, key as int) + acc, 0int)
    {
        if q[i] > 0 {
            product = product * q[i];
        }
        if q[i] == key {
            count = count + 1;
        }
    }
    
    proof {
        recursive_positive_product_fold_equiv(q@.map(|_, x: i32| x as int));
        recursive_count_fold_equiv(key as int, q@.map(|_, x: i32| x as int));
        assert(q@.map(|_, x: i32| x as int).subrange(0, q.len() as int) == q@.map(|_, x: i32| x as int));
    }
    
    (product, count)
}
// </vc-code>

fn main() {}

}