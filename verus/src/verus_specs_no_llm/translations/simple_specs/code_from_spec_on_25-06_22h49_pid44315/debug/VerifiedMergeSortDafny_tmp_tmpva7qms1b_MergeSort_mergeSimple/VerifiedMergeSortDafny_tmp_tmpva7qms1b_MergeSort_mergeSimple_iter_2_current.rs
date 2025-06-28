use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn sorted_seq(a: Seq<int>) -> bool {
    forall |i: int, j: int| 0 <= i < j < a.len() ==> a[i] <= a[j]
}

spec fn sorted_slice(a: &Vec<int>, start: int, end: int) -> bool
    requires 0 <= start <= end <= a.len()
{
    forall |i: int, j: int| start <= i < j < end ==> a[i] <= a[j]
}

// Helper spec function to check if all elements of one sequence appear in another
spec fn seq_contains_all(container: Seq<int>, contained: Seq<int>) -> bool {
    forall |i: int| 0 <= i < contained.len() ==> container.contains(contained[i])
}

// Implementation of mergeSimple - merges two sorted sequences
fn mergeSimple(a1: Seq<int>, a2: Seq<int>) -> (result: Seq<int>)
    requires 
        sorted_seq(a1),
        sorted_seq(a2)
    ensures 
        sorted_seq(result),
        result.len() == a1.len() + a2.len(),
        // All elements from a1 and a2 appear in result
        forall |x: int| a1.contains(x) || a2.contains(x) ==> result.contains(x),
        seq_contains_all(result, a1),
        seq_contains_all(result, a2)
{
    merge_recursive(a1, a2, 0, 0)
}

fn merge_recursive(a1: Seq<int>, a2: Seq<int>, i1: int, i2: int) -> (result: Seq<int>)
    requires
        sorted_seq(a1),
        sorted_seq(a2),
        0 <= i1 <= a1.len(),
        0 <= i2 <= a2.len()
    ensures
        sorted_seq(result),
        result.len() == (a1.len() - i1) + (a2.len() - i2),
        // Elements preservation
        forall |x: int| (a1.subrange(i1, a1.len() as int).contains(x) || 
                        a2.subrange(i2, a2.len() as int).contains(x)) ==> result.contains(x),
        seq_contains_all(result, a1.subrange(i1, a1.len() as int)),
        seq_contains_all(result, a2.subrange(i2, a2.len() as int))
    decreases a1.len() - i1 + a2.len() - i2
{
    if i1 >= a1.len() {
        // Take remaining elements from a2
        let remaining = a2.subrange(i2, a2.len() as int);
        assert(sorted_seq(remaining)) by {
            assert(forall |i: int, j: int| 0 <= i < j < remaining.len() ==> remaining[i] <= remaining[j]) by {
                assert(forall |i: int, j: int| 0 <= i < j < remaining.len() ==> a2[i2 + i] <= a2[i2 + j]);
            }
        };
        remaining
    } else if i2 >= a2.len() {
        // Take remaining elements from a1
        let remaining = a1.subrange(i1, a1.len() as int);
        assert(sorted_seq(remaining)) by {
            assert(forall |i: int, j: int| 0 <= i < j < remaining.len() ==> remaining[i] <= remaining[j]) by {
                assert(forall |i: int, j: int| 0 <= i < j < remaining.len() ==> a1[i1 + i] <= a1[i1 + j]);
            }
        };
        remaining
    } else if a1[i1] <= a2[i2] {
        // Take from a1
        let rest = merge_recursive(a1, a2, i1 + 1, i2);
        let result = seq![a1[i1]] + rest;
        
        // Prove sortedness
        assert(sorted_seq(result)) by {
            assert(forall |k: int| 0 <= k < rest.len() ==> a1[i1] <= rest[k]) by {
                if rest.len() > 0 {
                    // The first element of rest comes from either a1[i1+1..] or a2[i2..]
                    // In both cases, it's >= a1[i1] due to sortedness and our choice
                }
            }
        };
        
        result
    } else {
        // Take from a2
        let rest = merge_recursive(a1, a2, i1, i2 + 1);
        let result = seq![a2[i2]] + rest;
        
        // Prove sortedness
        assert(sorted_seq(result)) by {
            assert(forall |k: int| 0 <= k < rest.len() ==> a2[i2] <= rest[k]) by {
                if rest.len() > 0 {
                    // The first element of rest comes from either a1[i1..] or a2[i2+1..]
                    // In both cases, it's >= a2[i2] due to sortedness and our choice
                }
            }
        };
        
        result
    }
}

}