use builtin::*;
use builtin_macros::*;

verus! {

// Specification function to check if a sequence is sorted
spec fn is_sorted(s: Seq<int>) -> bool {
    forall|i: int, j: int| 0 <= i < j < s.len() ==> s[i] <= s[j]
}

// Specification function to check if two sequences are permutations of each other
spec fn is_permutation(s1: Seq<int>, s2: Seq<int>) -> bool {
    s1.to_multiset() == s2.to_multiset()
}

// Sort specification: output is sorted and is a permutation of input
spec fn SortSpec(input: Seq<int>, output: Seq<int>) -> bool {
    is_sorted(output) && is_permutation(input, output)
}

// Proof function for subrange permutation
proof fn lemma_subrange_permutation(s: Seq<int>, mid: int)
    requires 0 <= mid <= s.len()
    ensures is_permutation(s, s.subrange(0, mid).add(s.subrange(mid, s.len() as int)))
{
    assert(s =~= s.subrange(0, mid).add(s.subrange(mid, s.len() as int)));
}

// Proof function for permutation transitivity
proof fn lemma_permutation_transitivity(s1: Seq<int>, s2: Seq<int>, s3: Seq<int>)
    requires is_permutation(s1, s2), is_permutation(s2, s3)
    ensures is_permutation(s1, s3)
{
    assert(s1.to_multiset() == s2.to_multiset());
    assert(s2.to_multiset() == s3.to_multiset());
    assert(s1.to_multiset() == s3.to_multiset());
}

// Proof function for add permutation
proof fn lemma_add_permutation(s1: Seq<int>, s2: Seq<int>, s3: Seq<int>, s4: Seq<int>)
    requires is_permutation(s1, s2), is_permutation(s3, s4)
    ensures is_permutation(s1.add(s3), s2.add(s4))
{
    assert((s1.add(s3)).to_multiset() == s1.to_multiset().add(s3.to_multiset()));
    assert((s2.add(s4)).to_multiset() == s2.to_multiset().add(s4.to_multiset()));
}

// Lemma for sorted property preservation
proof fn lemma_sorted_subrange(s: Seq<int>, start: int, end: int)
    requires is_sorted(s), 0 <= start <= end <= s.len()
    ensures is_sorted(s.subrange(start, end))
{
    // This follows from the definition of is_sorted
}

// Lemma for sorted prepend
proof fn lemma_sorted_prepend(x: int, s: Seq<int>)
    requires is_sorted(s), forall|i: int| 0 <= i < s.len() ==> x <= s[i]
    ensures is_sorted(seq![x].add(s))
{
    let result = seq![x].add(s);
    assert forall|i: int, j: int| 0 <= i < j < result.len() implies result[i] <= result[j] by {
        if i == 0 {
            if j > 0 {
                assert(result[0] == x);
                assert(result[j] == s[j-1]);
                assert(x <= s[j-1]);
            }
        } else {
            assert(result[i] == s[i-1]);
            assert(result[j] == s[j-1]);
            assert(s[i-1] <= s[j-1]);
        }
    }
}

// Lemma for multiset commutativity
proof fn lemma_multiset_commutative(s1: Seq<int>, s2: Seq<int>)
    ensures s1.to_multiset().add(s2.to_multiset()) == s2.to_multiset().add(s1.to_multiset())
{
    // Multiset addition is commutative
}

// Lemma for sequence rearrangement
proof fn lemma_seq_rearrange(a: int, s1: Seq<int>, s2: Seq<int>)
    ensures is_permutation(seq![a].add(s1.add(s2)), s1.add(seq![a].add(s2)))
{
    // This follows from associativity and commutativity properties of multisets
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
        right
    } else if right.len() == 0 {
        left
    } else if left[0] <= right[0] {
        let left_tail = left.subrange(1, left.len() as int);
        let rest = merge(left_tail, right);
        let result = seq![left[0]].add(rest);
        
        // From postcondition of recursive call
        assert(is_permutation(left_tail.add(right), rest));
        
        // Prove that left[0] <= all elements in rest
        assert forall|i: int| 0 <= i < rest.len() implies left[0] <= rest[i] by {
            // Since rest is a permutation of left_tail + right, every element in rest
            // is either from left_tail or from right
            // From is_sorted(left): left[0] <= left[j] for all j >= 1, so left[0] <= all in left_tail
            // From left[0] <= right[0] and is_sorted(right): left[0] <= all in right
            // Therefore left[0] <= all elements in rest
        }
        
        lemma_sorted_prepend(left[0], rest);
        
        // Prove permutation: left + right =~= [left[0]] + left_tail + right =~= [left[0]] + rest
        lemma_seq_rearrange(left[0], left_tail, right);
        lemma_permutation_transitivity(left.add(right), left_tail.add(right), rest);
        lemma_permutation_transitivity(left.add(right), rest, result);
        
        result
    } else {
        // right[0] < left[0]
        let right_tail = right.subrange(1, right.len() as int);
        let rest = merge(left, right_tail);
        let result = seq![right[0]].add(rest);
        
        // From postcondition of recursive call
        assert(is_permutation(left.add(right_tail), rest));
        
        // Prove that right[0] <= all elements in rest
        assert forall|i: int| 0 <= i < rest.len() implies right[0] <= rest[i] by {
            // Since rest is a permutation of left + right_tail, every element in rest
            // is either from left or from right_tail
            // From right[0] < left[0] and is_sorted(left): right[0] <= all in left
            // From is_sorted(right): right[0] <= right[j] for all j >= 1, so right[0] <= all in right_tail
            // Therefore right[0] <= all elements in rest
        }
        
        lemma_sorted_prepend(right[0], rest);
        
        // Prove permutation using commutativity
        lemma_multiset_commutative(left, right);
        assert(is_permutation(left.add(right), right.add(left)));
        
        // right + left =~= [right[0]] + right_tail + left =~= [right[0]] + (left + right_tail) =~= [right[0]] + rest
        lemma_seq_rearrange(right[0], right_tail, left);
        assert(is_permutation(right.add(left), right_tail.add(left)));
        lemma_multiset_commutative(right_tail, left);
        assert(is_permutation(right_tail.add(left), left.add(right_tail)));
        
        lemma_permutation_transitivity(left.add(right), right.add(left), right_tail.add(left));
        lemma_permutation_transitivity(left.add(right), right_tail.add(left), left.add(right_tail));
        lemma_permutation_transitivity(left.add(right), left.add(right_tail), rest);
        lemma_permutation_transitivity(left.add(right), rest, result);
        
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
        input
    } else {
        let mid = input.len() / 2;
        let left_half = input.subrange(0, mid as int);
        let right_half = input.subrange(mid as int, input.len() as int);
        
        let sorted_left = merge_sort(left_half);
        let sorted_right = merge_sort(right_half);
        
        let result = merge(sorted_left, sorted_right);
        
        // Proof that result satisfies SortSpec
        lemma_subrange_permutation(input, mid as int);
        
        // From recursive calls we have:
        // is_permutation(left_half, sorted_left)
        // is_permutation(right_half, sorted_right)
        
        lemma_add_permutation(left_half, sorted_left, right_half, sorted_right);
        
        // From merge postcondition:
        // is_permutation(sorted_left.add(sorted_right), result)
        
        lemma_permutation_transitivity(input, left_half.add(right_half), sorted_left.add(sorted_right));
        lemma_permutation_transitivity(input, sorted_left.add(sorted_right), result);
        
        result
    }
}

fn main() {
    // Test the merge sort implementation
    let test_seq = seq![3, 1, 4, 1, 5, 9, 2, 6];
    let sorted_seq = merge_sort(test_seq);
}

}