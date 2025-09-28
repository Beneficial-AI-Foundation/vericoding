// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
proof fn lemma_seq_contains_index<A>(s: Seq<A>, i: int)
    requires
        0 <= i < s.len()
    ensures
        s.contains(s[i])
{
}

fn mem_vec(v: &Vec<i32>, x: i32) -> (b: bool)
    ensures
        b == v@.contains(x)
{
    let mut i: usize = 0;
    let mut found: bool = false;
    while i < v.len()
        invariant 0 <= (i as int) <= v.len() as int
        invariant found == (exists|j: int| 0 <= j < i as int && v@[j] == x)
        decreases (v.len() as int) - (i as int)
    {
        if v[i] == x {
            found = true;
        }
        i += 1;
    }
    found
}
// </vc-helpers>

// <vc-spec>
fn shared_elements(list1: &Vec<i32>, list2: &Vec<i32>) -> (shared: Vec<i32>)

    ensures
        forall|i: int|
            0 <= i < shared.len() ==> (list1@.contains(#[trigger] shared[i]) && list2@.contains(
                #[trigger] shared[i],
            )),
        forall|i: int, j: int| 0 <= i < j < shared.len() ==> shared[i] != shared[j],
// </vc-spec>
// <vc-code>
{
    let mut shared: Vec<i32> = Vec::new();
    let mut i: usize = 0;
    while i < list1.len()
        invariant 0 <= (i as int) <= list1.len() as int
        invariant forall|k: int| 0 <= k < shared.len() as int ==> list1@.contains(shared@[k]) && list2@.contains(shared@[k])
        invariant forall|k1: int, k2: int| 0 <= k1 < k2 < shared.len() as int ==> shared@[k1] != shared@[k2]
        decreases (list1.len() as int) - (i as int)
    {
        let x = list1[i];
        let in_list2 = mem_vec(list2, x);
        if in_list2 {
            let not_in_shared = !mem_vec(&shared, x);
            if not_in_shared {
                proof { lemma_seq_contains_index::<i32>(list1@, i as int); }
                shared.push(x);
            }
        }
        i += 1;
    }
    shared
}
// </vc-code>

}
fn main() {}