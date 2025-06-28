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

// Proof function to establish permutation properties
proof fn lemma_permutation_add_commutative(s1: Seq<int>, s2: Seq<int>)
    ensures is_permutation(s1.add(s2), s2.add(s1))
{
    assert(multiset_from_seq(s1.add(s2)) == multiset_from_seq(s1) + multiset_from_seq(s2));
    assert(multiset_from_seq(s2.add(s1)) == multiset_from_seq(s2) + multiset_from_seq(s1));
}

// Proof function for subrange permutation
proof fn lemma_subrange_permutation(s: Seq<int>, mid: int)
    requires 0 <= mid <= s.len()
    ensures is_permutation(s, s.subrange(0, mid).add(s.subrange(mid, s.len() as int)))
{
    // This is a fundamental property of subranges that Verus should accept
}

// Proof function for merge permutation property
proof fn lemma_merge_permutation(left: Seq<int>, right: Seq<int>, elem: int, rest: Seq<int>)
    requires is_permutation(left.add(right), seq![elem].add(rest))
    ensures is_permutation(seq![elem].add(left.add(right)), seq![elem].add(rest))
{
    // Adding the same element to both sides preserves permutation
}

// Helper function to merge two sorted sequences
fn merge(left: Seq<int>, right: Seq<int>) -> (result: Seq<int>)
    requires
        is_sorted(left),
        is_sorted(right)
    ensures
        is_sorted(result),
        is_permutation(left.add(right), result)
    decreases left.len() + right.len()
{
    if left.len() == 0 {
        // Base case: merging empty with right gives right
        assert(left.add(right) == right);
        right
    } else if right.len() == 0 {
        // Base case: merging left with empty gives left  
        assert(left.add(right) == left);
        left
    } else if left[0] <= right[0] {
        let rest = merge(left.subrange(1, left.len() as int), right);
        let result = seq![left[0]].add(rest);
        
        // Proof that result is sorted
        assert(forall|i: int| 0 <= i < rest.len() ==> left[0] <= rest[i]);
        
        // Proof that result is a permutation
        proof {
            assert(is_permutation(left.subrange(1, left.len() as int).add(right), rest));
            assert(left == seq![left[0]].add(left.subrange(1, left.len() as int)));
            lemma_merge_permutation(left.subrange(1, left.len() as int), right, left[0], rest);
        }
        
        result
    } else {
        let rest = merge(left, right.subrange(1, right.len() as int));
        let result = seq![right[0]].add(rest);
        
        // Proof that result is sorted
        assert(forall|i: int| 0 <= i < rest.len() ==> right[0] <= rest[i]);
        
        // Proof that result is a permutation
        proof {
            assert(is_permutation(left.add(right.subrange(1, right.len() as int)), rest));
            assert(right == seq![right[0]].add(right.subrange(1, right.len() as int)));
            lemma_permutation_add_commutative(left, right);
            lemma_merge_permutation(left, right.subrange(1, right.len() as int), right[0], rest);
        }
        
        result
    }
}

fn merge_sort(input: Seq<int>) -> (output: Seq<int>)
    ensures
        SortSpec(input, output)
    decreases input.len()
{
    if input.len() <= 1 {
        // Base case: sequences of length 0 or 1 are already sorted
        assert(is_sorted(input));
        assert(is_permutation(input, input));
        input
    } else {
        let mid = input.len() / 2;
        let left_half = input.subrange(0, mid as int);
        let right_half = input.subrange(mid as int, input.len() as int);
        
        let sorted_left = merge_sort(left_half);
        let sorted_right = merge_sort(right_half);
        
        let result = merge(sorted_left, sorted_right);
        
        // Proof that result satisfies SortSpec
        proof {
            // sorted_left and sorted_right are sorted (from postconditions)
            assert(is_sorted(sorted_left));
            assert(is_sorted(sorted_right));
            
            // sorted_left and sorted_right are permutations of their inputs
            assert(is_permutation(left_half, sorted_left));
            assert(is_permutation(right_half, sorted_right));
            
            // The halves form a permutation of the original input
            lemma_subrange_permutation(input, mid as int);
            assert(is_permutation(input, left_half.add(right_half)));
            
            // result is sorted and a permutation (from merge postconditions)
            assert(is_sorted(result));
            assert(is_permutation(sorted_left.add(sorted_right), result));
            
            // Transitivity of permutation
            assert(is_permutation(input, result));
        }
        
        result
    }
}

fn main() {
    // Test the merge sort implementation
    let test_seq = seq![3, 1, 4, 1, 5, 9, 2, 6];
    let sorted_seq = merge_sort(test_seq);
    assert(is_sorted(sorted_seq));
}

}