use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn threshold(thres: int, seq: Seq<int>) -> (seq_1: Seq<int>, seq_2: Seq<int>)
    ensures
        (forall|x: int| seq_1.contains(x) ==> x <= thres),
        (forall|x: int| seq_2.contains(x) ==> x > thres),
        seq_1.len() + seq_2.len() == seq.len(),
        seq_1.to_multiset().add(seq_2.to_multiset()) == seq.to_multiset(),
{
    let mut seq_1: Seq<int> = Seq::empty();
    let mut seq_2: Seq<int> = Seq::empty();
    let mut i = 0;
    
    while i < seq.len()
        invariant
            0 <= i <= seq.len(),
            (forall|x: int| seq_1.contains(x) ==> x <= thres),
            (forall|x: int| seq_2.contains(x) ==> x > thres),
            seq_1.len() + seq_2.len() == i,
            seq_1.to_multiset().add(seq_2.to_multiset()) == seq.subrange(0, i as int).to_multiset(),
    {
        let val = seq[i as int];
        if val <= thres {
            seq_1 = seq_1.push(val);
        } else {
            seq_2 = seq_2.push(val);
        }
        i = i + 1;
    }
    
    (seq_1, seq_2)
}

proof fn lemma_multiset_add_associative<T>(a: Multiset<T>, b: Multiset<T>, c: Multiset<T>)
    ensures a.add(b).add(c) == a.add(b.add(c))
{
}

proof fn lemma_multiset_equivalence(pivot: int, smaller: Seq<int>, larger: Seq<int>, rest: Seq<int>)
    requires
        smaller.to_multiset().add(larger.to_multiset()) == rest.to_multiset(),
    ensures
        seq![pivot].to_multiset().add(smaller.to_multiset()).add(larger.to_multiset()) 
            == seq![pivot].to_multiset().add(rest.to_multiset())
{
    lemma_multiset_add_associative(seq![pivot].to_multiset(), smaller.to_multiset(), larger.to_multiset());
}

proof fn lemma_contains_from_multiset<T>(seq1: Seq<T>, seq2: Seq<T>)
    requires seq1.to_multiset() == seq2.to_multiset()
    ensures forall|x: T| seq1.contains(x) <==> seq2.contains(x)
{
}

proof fn lemma_sequence_concatenation_multiset(pivot: int, seq1: Seq<int>, seq2: Seq<int>)
    ensures seq![pivot].add(seq1).add(seq2).to_multiset() == 
            seq![pivot].to_multiset().add(seq1.to_multiset()).add(seq2.to_multiset())
{
}

proof fn lemma_sequence_split_multiset(seq: Seq<int>)
    requires seq.len() > 0
    ensures seq.to_multiset() == seq![seq[0]].to_multiset().add(seq.subrange(1, seq.len() as int).to_multiset())
{
}

fn quick_sort(seq: Seq<int>) -> (seq_sorted: Seq<int>)
    ensures
        seq_sorted.to_multiset() == seq.to_multiset(),
        forall|i: int, j: int| 0 <= i < j < seq_sorted.len() ==> seq_sorted[i] <= seq_sorted[j],
    decreases seq.len()
{
    if seq.len() <= 1 {
        seq
    } else {
        let pivot = seq[0];
        let rest = seq.subrange(1, seq.len() as int);
        let (smaller, larger) = threshold(pivot, rest);
        
        let sorted_smaller = quick_sort(smaller);
        let sorted_larger = quick_sort(larger);
        
        let result = seq![pivot].add(sorted_smaller).add(sorted_larger);
        
        // Prove multiset equality
        proof {
            // From threshold postcondition
            assert(smaller.to_multiset().add(larger.to_multiset()) == rest.to_multiset());
            
            // From recursive calls
            assert(sorted_smaller.to_multiset() == smaller.to_multiset());
            assert(sorted_larger.to_multiset() == larger.to_multiset());
            
            // Combine these facts
            assert(sorted_smaller.to_multiset().add(sorted_larger.to_multiset()) == 
                   smaller.to_multiset().add(larger.to_multiset()));
            assert(sorted_smaller.to_multiset().add(sorted_larger.to_multiset()) == rest.to_multiset());
            
            // Use concatenation lemma
            lemma_sequence_concatenation_multiset(pivot, sorted_smaller, sorted_larger);
            assert(result.to_multiset() == 
                   seq![pivot].to_multiset().add(sorted_smaller.to_multiset()).add(sorted_larger.to_multiset()));
            
            // Use associativity
            lemma_multiset_add_associative(seq![pivot].to_multiset(), sorted_smaller.to_multiset(), sorted_larger.to_multiset());
            assert(result.to_multiset() == 
                   seq![pivot].to_multiset().add(sorted_smaller.to_multiset().add(sorted_larger.to_multiset())));
            assert(result.to_multiset() == seq![pivot].to_multiset().add(rest.to_multiset()));
            
            // Original sequence split
            lemma_sequence_split_multiset(seq);
            assert(seq.to_multiset() == seq![pivot].to_multiset().add(rest.to_multiset()));
            
            // Final equality
            assert(result.to_multiset() == seq.to_multiset());
        }
        
        // Prove sorting property
        proof {
            // Get properties from threshold
            assert(forall|x: int| smaller.contains(x) ==> x <= pivot);
            assert(forall|x: int| larger.contains(x) ==> x > pivot);
            
            // Transfer to sorted sequences using multiset preservation
            lemma_contains_from_multiset(smaller, sorted_smaller);
            lemma_contains_from_multiset(larger, sorted_larger);
            
            assert(forall|x: int| sorted_smaller.contains(x) ==> x <= pivot);
            assert(forall|x: int| sorted_larger.contains(x) ==> x > pivot);
            
            // The result is sorted by construction
            assert forall|i: int, j: int| 0 <= i < j < result.len() implies result[i] <= result[j] by {
                if i == 0 {
                    // pivot is at position 0
                    if j < 1 + sorted_smaller.len() {
                        // j is in sorted_smaller portion
                        assert(result[j] <= pivot);
                        assert(result[i] == pivot);
                    } else {
                        // j is in sorted_larger portion
                        assert(result[j] > pivot);
                        assert(result[i] == pivot);
                    }
                } else if i < 1 + sorted_smaller.len() {
                    if j < 1 + sorted_smaller.len() {
                        // both in sorted_smaller portion - use sorted property
                        let i_adj = i - 1;  
                        let j_adj = j - 1;
                        assert(0 <= i_adj < j_adj < sorted_smaller.len());
                        assert(sorted_smaller[i_adj] <= sorted_smaller[j_adj]);
                    } else {
                        // i in smaller, j in larger - smaller <= pivot < larger
                        assert(result[i] <= pivot);
                        assert(result[j] > pivot);
                    }
                } else {
                    // both in sorted_larger portion - use sorted property  
                    let i_adj = i - 1 - sorted_smaller.len();
                    let j_adj = j - 1 - sorted_smaller.len();
                    assert(0 <= i_adj < j_adj < sorted_larger.len());
                    assert(sorted_larger[i_adj] <= sorted_larger[j_adj]);
                }
            }
        }
        
        result
    }
}

}