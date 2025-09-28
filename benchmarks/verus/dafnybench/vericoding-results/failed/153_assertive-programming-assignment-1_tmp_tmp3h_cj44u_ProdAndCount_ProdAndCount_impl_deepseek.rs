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
spec fn seq_map_prod_property(q: Seq<int>, key: int) -> bool
    decreases q.len()
{
    &&& recursive_positive_product(q) == q.fold(1, |acc: int, x: int| if x <= 0 { acc } else { acc * x })
    &&& recursive_count(key, q) == q.fold(0, |acc: int, x: int| if x == key { acc + 1 } else { acc })
}

proof fn seq_map_prod_lemma(q: Seq<int>, key: int)
    ensures
        recursive_positive_product(q) == q.fold(1, |acc: int, x: int| if x <= 0 { acc } else { acc * x }),
    ensures
        recursive_count(key, q) == q.fold(0, |acc: int, x: int| if x == key { acc + 1 } else { acc }),
    decreases q.len()
{
    if q.len() == 0 {
    } else {
        let subq = q.subrange(1, q.len() as int);
        seq_map_prod_lemma(subq, key);
        assert(q[0] <= 0 || q[0] > 0);
    }
}

proof fn recursive_positive_product_subrange_lemma(q: Seq<int>, i: int)
    requires
        0 <= i <= q.len(),
    ensures
        recursive_positive_product(q.subrange(0, i)) == q.subrange(0, i).fold(1, |acc: int, x: int| if x <= 0 { acc } else { acc * x }),
    decreases i
{
    if i == 0 {
    } else {
        recursive_positive_product_subrange_lemma(q, i - 1);
    }
}

proof fn recursive_count_subrange_lemma(q: Seq<int>, key: int, i: int)
    requires
        0 <= i <= q.len(),
    ensures
        recursive_count(key, q.subrange(0, i)) == q.subrange(0, i).fold(0, |acc: int, x: int| if x == key { acc + 1 } else { acc }),
    decreases i
{
    if i == 0 {
    } else {
        recursive_count_subrange_lemma(q, key, i - 1);
    }
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
    let mut i: usize = 0;
    
    while i < q.len()
        invariant
            0 <= i <= q.len(),
            prod == recursive_positive_product(q@.subrange(0, i as int)) as i32,
            count == recursive_count(key as int, q@.subrange(0, i as int)) as u32,
        decreases q.len() - i
    {
        let elem = q[i];
        if elem <= 0 {
            // Skip negative elements in product
        } else {
            prod *= elem;
        }
        if elem == key {
            count += 1;
        }
        i += 1;
    }
    (prod, count)
}
// </vc-code>

fn main() {}

}