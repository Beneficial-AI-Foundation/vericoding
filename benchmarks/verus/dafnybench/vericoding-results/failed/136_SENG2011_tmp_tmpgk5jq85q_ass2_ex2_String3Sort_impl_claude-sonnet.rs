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
proof fn lemma_sorted_three(a: char, b: char, c: char)
    requires a <= b <= c
    ensures sorted(seq![a, b, c], 0, 3)
{
    assert(forall|j: int, k: int| 0 <= j < k < 3 ==> seq![a, b, c][j] <= seq![a, b, c][k]);
}

proof fn lemma_multiset_preservation(a0: char, a1: char, a2: char, b0: char, b1: char, b2: char)
    requires seq![b0, b1, b2].to_multiset() == seq![a0, a1, a2].to_multiset()
    ensures seq![a0, a1, a2].to_multiset() == seq![b0, b1, b2].to_multiset()
{
}
// </vc-helpers>

// <vc-spec>
fn string3_sort(a: Seq<char>) -> (b: Seq<char>)
    requires 
        a.len() == 3,
    ensures 
        sorted(b, 0, b.len() as int),
        a.len() == b.len(),
        seq![b[0], b[1], b[2]].to_multiset() == seq![a[0], a[1], a[2]].to_multiset(),
// </vc-spec>
// <vc-code>
{
    let a0 = a@[0];
    let a1 = a@[1];
    let a2 = a@[2];
    
    let result = if a0 <= a1 && a1 <= a2 {
        seq![a0, a1, a2]
    } else if a0 <= a2 && a2 <= a1 {
        seq![a0, a2, a1]
    } else if a1 <= a0 && a0 <= a2 {
        seq![a1, a0, a2]
    } else if a1 <= a2 && a2 <= a0 {
        seq![a1, a2, a0]
    } else if a2 <= a0 && a0 <= a1 {
        seq![a2, a0, a1]
    } else {
        seq![a2, a1, a0]
    };
    
    proof {
        if a0 <= a1 && a1 <= a2 {
            lemma_sorted_three(a0, a1, a2);
        } else if a0 <= a2 && a2 <= a1 {
            lemma_sorted_three(a0, a2, a1);
        } else if a1 <= a0 && a0 <= a2 {
            lemma_sorted_three(a1, a0, a2);
        } else if a1 <= a2 && a2 <= a0 {
            lemma_sorted_three(a1, a2, a0);
        } else if a2 <= a0 && a0 <= a1 {
            lemma_sorted_three(a2, a0, a1);
        } else {
            lemma_sorted_three(a2, a1, a0);
        }
    }
    
    result
}
// </vc-code>

fn main() {
}

}