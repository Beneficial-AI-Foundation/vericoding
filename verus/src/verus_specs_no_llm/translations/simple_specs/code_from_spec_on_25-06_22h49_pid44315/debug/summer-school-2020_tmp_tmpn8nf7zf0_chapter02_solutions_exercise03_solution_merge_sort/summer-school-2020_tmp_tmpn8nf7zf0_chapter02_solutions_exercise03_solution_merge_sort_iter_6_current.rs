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
        assert(left.add(right) =~= right);
        right
    } else if right.len() == 0 {
        assert(left.add(right) =~= left);
        left
    } else if left[0] <= right[0] {
        let rest = merge(left.subrange(1, left.len() as int), right);
        let result = seq![left[0]].add(rest);
        
        // Proof that left[0] <= all elements in rest
        assert forall|i: int| 0 <= i < rest.len() implies left[0] <= rest[i] by {
            // rest is a merge of left.subrange(1, left.len()) and right
            // Since left is sorted, left[0] <= all elements in left.subrange(1, left.len())
            // Since left[0] <= right[0] and right is sorted, left[0] <= all elements in right
            // Therefore left[0] <= all elements in rest
        }
        
        // Proof that result is sorted
        lemma_sorted_prepend(left[0], rest);
        
        // Proof that result is a permutation
        assert(is_permutation(left.add(right), result)) by {
            let left_tail = left.subrange(1, left.len() as int);
            assert(left =~= seq![left[0]].add(left_tail));
            assert(is_permutation(left_tail.add(right), rest));
            
            // Use the fact that permutation is preserved under prepending the same element
            assert(seq![left[0]].add(left_tail).add(right) =~= left.add(right));
            assert(seq![left[0]].add(left_tail.add(right)) =~= seq![left[0]].add(left_tail).add(right));
            
            // By properties of multisets and permutation
            lemma_add_permutation(seq![left[0]], seq![left[0]], left_tail.add(right), rest);
            assert(is_permutation(seq![left[0]].add(left_tail.add(right)), seq![left[0]].add(rest)));
        };
        
        result
    } else {
        // right[0] < left[0]
        let rest = merge(left, right.subrange(1, right.len() as int));
        let result = seq![right[0]].add(rest);
        
        // Proof that right[0] <= all elements in rest
        assert forall|i: int| 0 <= i < rest.len() implies right[0] <= rest[i] by {
            // rest is a merge of left and right.subrange(1, right.len())
            // Since right[0] < left[0], right[0] <= all elements in left
            // Since right is sorted, right[0] <= all elements in right.subrange(1, right.len())
            // Therefore right[0] <= all elements in rest
        }
        
        // Proof that result is sorted
        lemma_sorted_prepend(right[0], rest);
        
        // Proof that result is a permutation
        assert(is_permutation(left.add(right), result)) by {
            let right_tail = right.subrange(1, right.len() as int);
            assert(right =~= seq![right[0]].add(right_tail));
            assert(is_permutation(left.add(right_tail), rest));
            
            // Use commutativity and associativity of sequence addition
            assert(left.add(right) =~= left.add(seq![right[0]].add(right_tail)));
            assert(left.add(seq![right[0]].add(right_tail)) =~= seq![right[0]].add(left.add(right_tail)));
            
            lemma_add_permutation(seq![right[0]], seq![right[0]], left.add(right_tail), rest);
            assert(is_permutation(seq![right[0]].add(left.add(right_tail)), seq![right[0]].add(rest)));
        };
        
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
        assert(SortSpec(input, result)) by {
            // result is sorted (from merge postcondition)
            assert(is_sorted(result));
            
            // Prove permutation through transitivity chain
            lemma_subrange_permutation(input, mid as int);
            assert(is_permutation(input, left_half.add(right_half)));
            
            // From recursive calls
            assert(is_permutation(left_half, sorted_left));
            assert(is_permutation(right_half, sorted_right));
            
            // Combine the permutations
            lemma_add_permutation(left_half, sorted_left, right_half, sorted_right);
            assert(is_permutation(left_half.add(right_half), sorted_left.add(sorted_right)));
            
            // From merge postcondition
            assert(is_permutation(sorted_left.add(sorted_right), result));
            
            // Chain the permutations
            lemma_permutation_transitivity(input, left_half.add(right_half), sorted_left.add(sorted_right));
            lemma_permutation_transitivity(input, sorted_left.add(sorted_right), result);
            assert(is_permutation(input, result));
        };
        
        result
    }
}

fn main() {
    // Test the merge sort implementation
    let test_seq = seq![3, 1, 4, 1, 5, 9, 2, 6];
    let sorted_seq = merge_sort(test_seq);
}

}