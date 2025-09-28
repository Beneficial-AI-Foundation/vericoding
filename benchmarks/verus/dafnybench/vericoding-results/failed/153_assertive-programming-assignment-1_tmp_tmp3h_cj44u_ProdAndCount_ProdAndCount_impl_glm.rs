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
proof fn lemma_prody_county_map<A>(q: Seq<A>, f: spec fn(A) -> int, g: spec fn(A) -> int)
    decreases q.len()
{
    if q.len() == 0 {
        assert(Seq::<int>::new(0, |i: int| f(q[i])).map(|_, x: int| g(x)) == Seq::<int>::new(0, |i: int| g(f(q[i]))));
    } else {
        lemma_prody_county_map(q.subrange(1, q.len() as int), f, g);
        assert(Seq::<int>::new(q.len(), |i: int| f(q[i])).map(|_, x: int| g(x)) ==
// </vc-helpers>

// <vc-spec>
fn prod_and_count(q: &[i32], key: i32) -> (i32, u32)
    ensures |result: (i32, u32)| 
        result.0 == recursive_positive_product(q@.map(|_, x: i32| x as int)) &&
        result.1 == recursive_count(key as int, q@.map(|_, x: i32| x as int)) as u32
// </vc-spec>
// <vc-code>
proof fn lemma_prody_county_map<A>(q: Seq<A>, f: spec fn(A) -> int, g: spec fn(A) -> int)
    decreases q.len()
{
    if q.len() == 0 {
        assert(Seq::<int>::new(0, |i: int| f(q[i])).map(|_, x: int| g(x)) == Seq::<int>::new(0, |i: int| g(f(q[i]))));
    } else {
        lemma_prody_county_map(q.subrange(1, q.len() as int), f, g);
        assert(Seq::<int>::new(q.len(), |i: int| f(q[i])).map(|_, x: int| g(x)) ==
// </vc-code>

fn main() {}

}