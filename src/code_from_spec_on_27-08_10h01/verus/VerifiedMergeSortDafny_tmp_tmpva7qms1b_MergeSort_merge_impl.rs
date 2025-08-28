use vstd::prelude::*;

verus! {

spec fn merged(a1: Seq<int>, a2: Seq<int>, b: &Vec<int>, start: int, end: int) -> bool {
    &&& end - start == a2.len() + a1.len()
    &&& 0 <= start <= end <= b.len()
    &&& a1.to_multiset().add(a2.to_multiset()) == b@.subrange(start, end).to_multiset()
}

spec fn sorted_slice(a: &Vec<int>, start: int, end: int) -> bool {
    &&& 0 <= start <= end <= a.len()
    &&& forall|i: int, j: int| start <= i <= j < end ==> a@[i] <= a@[j]
}

spec fn sorted_seq(a: Seq<int>) -> bool {
    forall|i: int, j: int| 0 <= i <= j < a.len() ==> a[i] <= a[j]
}

spec fn sorted(a: &Vec<int>) -> bool {
    forall|i: int, j: int| 0 <= i < j < a.len() ==> a@[i] <= a@[j]
}

// <vc-helpers>
proof fn lemma_multiset_merge_property(a1: Seq<int>, a2: Seq<int>, b: Seq<int>)
    requires
        a1.len() + a2.len() == b.len(),
        forall|i: int| 0 <= i < a1.len() ==> b[i] == a1[i],
        forall|i: int| 0 <= i < a2.len() ==> b[a1.len() + i] == a2[i],
    ensures
        b.to_multiset() == a1.to_multiset().add(a2.to_multiset())
{
    let split_point = a1.len();
    assert(b == a1.add(a2));
}

proof fn lemma_sorted_merge_maintains_order(a1: Seq<int>, a2: Seq<int>, result: Seq<int>, i1: int, i2: int, pos: int)
    requires
        sorted_seq(a1),
        sorted_seq(a2),
        0 <= i1 <= a1.len(),
        0 <= i2 <= a2.len(),
        0 <= pos <= result.len(),
        pos == i1 + i2,
        forall|k: int| 0 <= k < pos ==> {
            let from_a1 = k < i1;
            let idx_in_a1 = if from_a1 { k } else { k - i1 };
            let idx_in_a2 = if from_a1 { 0 } else { k - i1 };
            from_a1 ==> (0 <= idx_in_a1 < a1.len() && result[k] == a1[idx_in_a1])
        },
    ensures
        forall|k1: int, k2: int| 0 <= k1 < k2 < pos ==> result[k1] <= result[k2]
{}
// </vc-helpers>

// <vc-spec>
// <vc-spec>
fn merge(a1: Seq<int>, a2: Seq<int>, start: int, end: int, b: &mut Vec<int>)
    requires 
        sorted_seq(a1),
        sorted_seq(a2),
        end - start == a1.len() + a2.len(),
        0 <= start < end < a1.len() && end <= a2.len() < old(b).len(),
        end < a1.len() && end < a2.len(),
        old(b).len() == a2.len() + a1.len(),
    ensures 
        sorted_slice(b, start, end),
        merged(a1, a2, b, start, end),
// </vc-spec>
// </vc-spec>

// <vc-code>
{
    let mut i1: nat = 0;
    let mut i2: nat = 0;
    let mut pos: usize = start as usize;
    
    while i1 < a1.len() && i2 < a2.len()
        invariant
            0 <= i1 <= a1.len(),
            0 <= i2 <= a2.len(),
            pos == start + i1 + i2,
            pos <= b.len(),
            sorted_slice(b, start, pos as int),
            forall|k: int| start <= k < pos ==> {
                exists|k1: int, k2: int| 0 <= k1 <= i1 && 0 <= k2 <= i2 && k1 + k2 == k - start &&
                ((k1 < i1 && b@[k] == a1[k1]) || (k2 < i2 && b@[k] == a2[k2]))
            },
    {
        if a1@[i1 as int] <= a2@[i2 as int] {
            b.set(pos, a1@[i1 as int]);
            i1 = i1 + 1;
        } else {
            b.set(pos, a2@[i2 as int]);
            i2 = i2 + 1;
        }
        pos += 1;
    }
    
    while i1 < a1.len()
        invariant
            i1 <= a1.len(),
            i2 == a2.len(),
            pos == start + i1 + i2,
            pos <= b.len(),
            sorted_slice(b, start, pos as int),
    {
        b.set(pos, a1@[i1 as int]);
        i1 = i1 + 1;
        pos += 1;
    }
    
    while i2 < a2.len()
        invariant
            i1 == a1.len(),
            i2 <= a2.len(),
            pos == start + i1 + i2,
            pos <= b.len(),
            sorted_slice(b, start, pos as int),
    {
        b.set(pos, a2@[i2 as int]);
        i2 = i2 + 1;
        pos += 1;
    }
}
// </vc-code>

fn main() {}

}