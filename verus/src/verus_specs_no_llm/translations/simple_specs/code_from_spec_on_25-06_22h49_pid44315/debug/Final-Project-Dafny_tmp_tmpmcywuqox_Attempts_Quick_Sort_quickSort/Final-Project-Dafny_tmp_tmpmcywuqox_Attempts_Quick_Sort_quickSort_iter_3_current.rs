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

proof fn lemma_sorted_concatenation(pivot: int, sorted_smaller: Seq<int>, sorted_larger: Seq<int>)
    requires
        forall|i: int, j: int| 0 <= i < j < sorted_smaller.len() ==> sorted_smaller[i] <= sorted_smaller[j],
        forall|i: int, j: int| 0 <= i < j < sorted_larger.len() ==> sorted_larger[i] <= sorted_larger[j],
        forall|x: int| sorted_smaller.contains(x) ==> x <= pivot,
        forall|x: int| sorted_larger.contains(x) ==> x > pivot,
    ensures
        forall|i: int, j: int| 0 <= i < j < seq![pivot].add(sorted_smaller).add(sorted_larger).len() 
            ==> seq![pivot].add(sorted_smaller).add(sorted_larger)[i] <= seq![pivot].add(sorted_smaller).add(sorted_larger)[j]
{
    let result = seq![pivot].add(sorted_smaller).add(sorted_larger);
    assert forall|i: int, j: int| 0 <= i < j < result.len() implies result[i] <= result[j] by {
        if i == 0 {
            // pivot is at position 0
            if j < 1 + sorted_smaller.len() {
                // j is in sorted_smaller portion
                assert(sorted_smaller.contains(result[j]));
                assert(result[j] <= pivot);
            } else {
                // j is in sorted_larger portion  
                assert(sorted_larger.contains(result[j]));
                assert(result[j] > pivot);
                assert(pivot <= result[j]);
            }
        } else if i < 1 + sorted_smaller.len() {
            if j < 1 + sorted_smaller.len() {
                // both in sorted_smaller
                let i_smaller = i - 1;
                let j_smaller = j - 1;
                assert(0 <= i_smaller < j_smaller < sorted_smaller.len());
                assert(sorted_smaller[i_smaller] <= sorted_smaller[j_smaller]);
                assert(result[i] == sorted_smaller[i_smaller]);
                assert(result[j] == sorted_smaller[j_smaller]);
            } else {
                // i in sorted_smaller, j in sorted_larger
                let i_smaller = i - 1;
                let j_larger = j - 1 - sorted_smaller.len();
                assert(result[i] == sorted_smaller[i_smaller]);
                assert(result[j] == sorted_larger[j_larger]);
                assert(sorted_smaller.contains(result[i]));
                assert(sorted_larger.contains(result[j]));
                assert(result[i] <= pivot);
                assert(result[j] > pivot);
            }
        } else {
            // both in sorted_larger
            let i_larger = i - 1 - sorted_smaller.len();
            let j_larger = j - 1 - sorted_smaller.len();
            assert(0 <= i_larger < j_larger < sorted_larger.len());
            assert(sorted_larger[i_larger] <= sorted_larger[j_larger]);
            assert(result[i] == sorted_larger[i_larger]);
            assert(result[j] == sorted_larger[j_larger]);
        }
    }
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
            // From threshold postcondition: smaller.to_multiset().add(larger.to_multiset()) == rest.to_multiset()
            lemma_multiset_equivalence(pivot, sorted_smaller, sorted_larger, rest);
            // From quicksort postconditions: sorted_smaller.to_multiset() == smaller.to_multiset()
            // and sorted_larger.to_multiset() == larger.to_multiset()
            assert(result.to_multiset() == seq![pivot].to_multiset().add(sorted_smaller.to_multiset()).add(sorted_larger.to_multiset()));
            assert(seq![pivot].to_multiset().add(rest.to_multiset()) == seq.to_multiset());
        }
        
        // Prove sorting property
        proof {
            // From threshold: elements in smaller <= pivot, elements in larger > pivot
            // From quicksort: sorted_smaller and sorted_larger are sorted
            // Need to transfer properties from smaller/larger to sorted_smaller/sorted_larger
            assert forall|x: int| sorted_smaller.contains(x) implies x <= pivot by {
                assert(smaller.contains(x)); // from quicksort multiset property
            }
            assert forall|x: int| sorted_larger.contains(x) implies x > pivot by {
                assert(larger.contains(x)); // from quicksort multiset property  
            }
            lemma_sorted_concatenation(pivot, sorted_smaller, sorted_larger);
        }
        
        result
    }
}

}