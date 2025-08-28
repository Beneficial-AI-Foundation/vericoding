use vstd::prelude::*;

verus! {

// verifies
// check that string between indexes low and high-1 are sorted
spec fn sorted(a: Seq<char>, low: int, high: int) -> bool
    recommends 0 <= low <= high <= a.len()
{ 
    forall|j: int, k: int| low <= j < k < high ==> a[j] <= a[k]
}

// <vc-helpers>
proof fn lemma_sorted_three_chars(a: char, b: char, c: char)
    ensures sorted(seq![a, b, c], 0, 3) <==> (a <= b && b <= c)
{
}

proof fn lemma_multiset_preservation(a: Seq<char>, b: Seq<char>)
    requires a.len() == 3, b.len() == 3,
        b == seq![a[0], a[1], a[2]]
    ensures seq![b[0], b[1], b[2]].to_multiset() == seq![a[0], a[1], a[2]].to_multiset()
{
}
// </vc-helpers>

// <vc-spec>
// <vc-spec>
fn string3_sort(a: Seq<char>) -> (b: Seq<char>)
    requires 
        a.len() == 3,
    ensures 
        sorted(b, 0, b.len() as int),
        a.len() == b.len(),
        seq![b[0], b[1], b[2]].to_multiset() == seq![a[0], a[1], a[2]].to_multiset(),
// </vc-spec>
// </vc-spec>

// <vc-code>
{
    let x = a[0];
    let y = a[1]; 
    let z = a[2];
    
    let result = if x <= y && y <= z {
        seq![x, y, z]
    } else if x <= z && z <= y {
        seq![x, z, y]
    } else if y <= x && x <= z {
        seq![y, x, z]
    } else if y <= z && z <= x {
        seq![y, z, x]
    } else if z <= x && x <= y {
        seq![z, x, y]
    } else {
        seq![z, y, x]
    };
    
    proof {
        lemma_sorted_three_chars(result[0], result[1], result[2]);
        lemma_multiset_preservation(a, result);
    }
    
    result
}
// </vc-code>

fn main() {
}

}