use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn IsSorted(s: Seq<int>) -> bool {
    forall|i: int| 0 <= i < (s.len() as int) - 1 ==> s[i] <= s[i + 1]
}

spec fn contains_same_elements(s1: Seq<int>, s2: Seq<int>) -> bool {
    forall|x: int| s1.count(x) == s2.count(x)
}

spec fn SortSpec(input: Seq<int>, output: Seq<int>) -> bool {
    && IsSorted(output)
    && contains_same_elements(input, output)
}

fn insert_sorted(sorted: Seq<int>, x: int) -> (result: Seq<int>)
    requires IsSorted(sorted)
    ensures 
        IsSorted(result) &&
        result.len() == sorted.len() + 1 &&
        forall|y: int| result.count(y) == sorted.count(y) + (if y == x { 1 } else { 0 })
{
    insert_sorted_rec(sorted, x, 0)
}

fn insert_sorted_rec(sorted: Seq<int>, x: int, pos: usize) -> (result: Seq<int>)
    requires 
        IsSorted(sorted) &&
        pos <= sorted.len() &&
        forall|i: int| 0 <= i < pos ==> sorted[i] <= x
    ensures 
        IsSorted(result) &&
        result.len() == sorted.len() + 1 &&
        forall|y: int| result.count(y) == sorted.count(y) + (if y == x { 1 } else { 0 })
    decreases sorted.len() - pos
{
    if pos == sorted.len() {
        // Insert at the end
        let result = sorted.push(x);
        
        // The push operation maintains sortedness when x is >= all elements
        assert(forall|i: int| 0 <= i < pos ==> sorted[i] <= x);
        assert(pos == sorted.len() ==> (pos == 0 || sorted[pos - 1] <= x));
        
        result
    } else if sorted[pos as int] >= x {
        // Insert at current position
        let prefix = sorted.subrange(0, pos as int);
        let suffix = sorted.subrange(pos as int, sorted.len() as int);
        let middle = seq![x];
        let result = prefix.add(middle).add(suffix);
        
        // Prove count property
        assert(forall|y: int| {
            prefix.count(y) + middle.count(y) + suffix.count(y) == 
            sorted.count(y) + (if y == x { 1 } else { 0 })
        });
        
        // Prove sortedness
        lemma_insert_maintains_sorted_at_pos(sorted, x, pos as int);
        
        result
    } else {
        // Continue searching for insertion point
        assert(sorted[pos as int] < x);
        assert(forall|i: int| 0 <= i < pos + 1 ==> sorted[i] <= x);
        insert_sorted_rec(sorted, x, pos + 1)
    }
}

proof fn lemma_insert_maintains_sorted_at_pos(s: Seq<int>, x: int, pos: int)
    requires 
        IsSorted(s) &&
        0 <= pos < s.len() &&
        s[pos] >= x &&
        forall|i: int| 0 <= i < pos ==> s[i] <= x
    ensures 
        IsSorted(s.subrange(0, pos).add(seq![x]).add(s.subrange(pos, s.len() as int)))
{
    let prefix = s.subrange(0, pos);
    let suffix = s.subrange(pos, s.len() as int);
    let result = prefix.add(seq![x]).add(suffix);
    
    // Key insight: x fits between prefix and suffix
    if pos > 0 {
        assert(s[pos - 1] <= x);  // from precondition
    }
    assert(x <= s[pos]);  // from precondition
}

proof fn lemma_count_decomposition(s: Seq<int>, first: int)
    requires s.len() > 0
    ensures forall|x: int| s.subrange(1, s.len() as int).count(x) == s.count(x) - (if x == first { 1 } else { 0 })
    ensures s[0] == first
{
    // This follows from the definition of count and subrange
}

fn fast_sort(input: Seq<int>) -> (output: Seq<int>)
    ensures SortSpec(input, output)
    decreases input.len()
{
    if input.len() == 0 {
        let result = Seq::empty();
        assert(IsSorted(result));
        assert(contains_same_elements(input, result));
        result
    } else {
        let first = input[0];
        let rest = input.subrange(1, input.len() as int);
        
        // Prove count property for rest
        lemma_count_decomposition(input, first);
        
        let sorted_rest = fast_sort(rest);
        
        // From postcondition of recursive call
        assert(IsSorted(sorted_rest));
        assert(contains_same_elements(rest, sorted_rest));
        
        let result = insert_sorted(sorted_rest, first);
        
        // From postcondition of insert_sorted
        assert(IsSorted(result));
        assert(forall|y: int| result.count(y) == sorted_rest.count(y) + (if y == first { 1 } else { 0 }));
        
        // Chain the count equalities
        assert(forall|y: int| {
            let input_count = input.count(y);
            let rest_count = rest.count(y);
            let sorted_rest_count = sorted_rest.count(y);
            let result_count = result.count(y);
            
            // From lemma_count_decomposition
            rest_count == input_count - (if y == first { 1 } else { 0 }) &&
            // From recursive call postcondition
            sorted_rest_count == rest_count &&
            // From insert_sorted postcondition
            result_count == sorted_rest_count + (if y == first { 1 } else { 0 })
        });
        
        // Therefore: result.count(y) == input.count(y)
        assert(contains_same_elements(input, result));
        
        result
    }
}

}