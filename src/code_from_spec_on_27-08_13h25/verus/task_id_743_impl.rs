use vstd::prelude::*;

verus! {

spec fn rotation_split(len: usize, n: usize) -> (result: int) {
    len - (n % len)
}
// pure-end

// <vc-helpers>
spec fn rotation_split(len: usize, n: usize) -> int {
    len - (n % len)
}

proof fn seq_subrange_add<T>(s1: Seq<T>, s2: Seq<T>, full: Seq<T>, split: int)
    requires
        full.len() == s1.len() + s2.len(),
        split >= 0,
        split <= full.len(),
        s1 == full.subrange(split, full.len() as int),
        s2 == full.subrange(0, split),
    ensures
        s1.add(s2) == full,
{
}
// </vc-helpers>

// <vc-spec>
fn rotate_right(list: &Vec<u32>, n: usize) -> (new_list: Vec<u32>)
    // pre-conditions-start
    requires
        list.len() > 0,
    // pre-conditions-end
    // post-conditions-start
    ensures
        new_list.len() == list.len(),
        new_list@ == list@.subrange(rotation_split(list.len(), n) as int, list@.len() as int).add(
            list@.subrange(0, rotation_split(list.len(), n) as int),
        ),
    // post-conditions-end
// </vc-spec>

// <vc-code>
fn rotate_right(list: &Vec<u32>, n: usize) -> (new_list: Vec<u32>)
    requires
        list.len() > 0,
    ensures
        new_list.len() == list.len(),
        new_list@ == list@.subrange(rotation_split(list.len(), n) as int, list@.len() as int).add(
            list@.subrange(0, rotation_split(list.len(), n) as int),
        ),
{
    let split = rotation_split(list.len(), n) as usize;
    let mut result = Vec::new();
    let mut i: usize = split;

    while i < list.len()
        invariant
            split <= list.len(),
            result.len() == i - split,
            forall |k: usize| k < result.len() ==> result@[k] == list@[k + split],
    {
        result.push(list@[i]);
        i = i + 1;
    }

    i = 0;
    while i < split
        invariant
            split <= list.len(),
            result.len() == list.len() - split + i,
            forall |k: usize| k < list.len() - split ==> result@[k] == list@[k + split],
            forall |k: usize| list.len() - split <= k < result.len() ==> result@[k] == list@[k - (list.len() - split)],
    {
        result.push(list@[i]);
        i = i + 1;
    }

    proof {
        seq_subrange_add(
            list@.subrange(split as int, list@.len() as int),
            list@.subrange(0, split as int),
            list@,
            split as int
        );
    }

    result
}
// </vc-code>

} // verus!

fn main() {}