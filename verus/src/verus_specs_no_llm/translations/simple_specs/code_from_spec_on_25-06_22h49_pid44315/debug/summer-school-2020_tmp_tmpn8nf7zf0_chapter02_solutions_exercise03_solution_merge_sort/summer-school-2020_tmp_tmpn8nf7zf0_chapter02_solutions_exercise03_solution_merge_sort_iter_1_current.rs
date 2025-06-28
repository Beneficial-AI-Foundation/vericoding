use builtin::*;
use builtin_macros::*;

verus! {

// Specification function to check if a sequence is sorted
spec fn is_sorted(s: Seq<int>) -> bool {
    forall|i: int, j: int| 0 <= i < j < s.len() ==> s[i] <= s[j]
}

// Specification function to check if two sequences are permutations of each other
spec fn is_permutation(s1: Seq<int>, s2: Seq<int>) -> bool {
    multiset_from_seq(s1) == multiset_from_seq(s2)
}

// Helper function to convert sequence to multiset
spec fn multiset_from_seq(s: Seq<int>) -> Multiset<int>
    decreases s.len()
{
    if s.len() == 0 {
        Multiset::empty()
    } else {
        multiset_from_seq(s.drop_last()).insert(s[s.len() - 1])
    }
}

// Sort specification: output is sorted and is a permutation of input
spec fn SortSpec(input: Seq<int>, output: Seq<int>) -> bool {
    is_sorted(output) && is_permutation(input, output)
}

// Helper function to merge two sorted sequences
fn merge(left: Seq<int>, right: Seq<int>) -> (result: Seq<int>)
    requires
        is_sorted(left),
        is_sorted(right)
    ensures
        is_sorted(result),
        is_permutation(left.add(right), result)
{
    if left.len() == 0 {
        right
    } else if right.len() == 0 {
        left
    } else if left[0] <= right[0] {
        seq![left[0]].add(merge(left.subrange(1, left.len() as int), right))
    } else {
        seq![right[0]].add(merge(left, right.subrange(1, right.len() as int)))
    }
}

fn merge_sort(input: Seq<int>) -> (output: Seq<int>)
    ensures
        SortSpec(input, output)
    decreases input.len()
{
    if input.len() <= 1 {
        input
    } else {
        let mid = input.len() / 2;
        let left_half = input.subrange(0, mid as int);
        let right_half = input.subrange(mid as int, input.len() as int);
        
        let sorted_left = merge_sort(left_half);
        let sorted_right = merge_sort(right_half);
        
        merge(sorted_left, sorted_right)
    }
}

fn main() {
    // Test the merge sort implementation
    let test_seq = seq![3, 1, 4, 1, 5, 9, 2, 6];
    let sorted_seq = merge_sort(test_seq);
    assert(is_sorted(sorted_seq));
}

}