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
        
        // Proof that x is >= all elements in sorted
        assert(forall|i: int| 0 <= i < sorted.len() ==> sorted[i] <= x);
        
        // Prove sortedness is maintained
        assert(forall|i: int| 0 <= i < result.len() - 1 ==> {
            if i < sorted.len() - 1 {
                result[i] == sorted[i] && result[i + 1] == sorted[i + 1] && sorted[i] <= sorted[i + 1]
            } else if i == sorted.len() - 1 {
                result[i] == sorted[i] && result[i + 1] == x && sorted[i] <= x
            } else {
                false
            }
        });
        
        result
    } else if sorted[pos as int] >= x {
        // Insert at current position
        let prefix = sorted.subrange(0, pos as int);
        let suffix = sorted.subrange(pos as int, sorted.len() as int);
        let middle = seq![x];
        let temp = prefix.add(middle);
        let result = temp.add(suffix);
        
        // Prove count property using sequence properties
        assert(forall|y: int| {
            result.count(y) == prefix.count(y) + middle.count(y) + suffix.count(y)
        });
        assert(forall|y: int| {
            prefix.count(y) + suffix.count(y) == sorted.count(y)
        });
        assert(forall|y: int| {
            middle.count(y) == (if y == x { 1 } else { 0 })
        });
        
        // Prove sortedness using the lemma
        lemma_insert_maintains_sorted_at_pos(sorted, x, pos as int);
        
        result
    } else {
        // Continue searching for insertion point
        assert(sorted[pos as int] < x);
        // Strengthen the invariant for the recursive call
        assert(forall|i: int| 0 <= i < pos + 1 ==> sorted[i] <= x) by {
            assert(forall|i: int| 0 <= i < pos ==> sorted[i] <= x);
            assert(sorted[pos as int] < x);
            assert(sorted[pos as int] <= x);
        };
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
    let middle = seq![x];
    let temp = prefix.add(middle);
    let result = temp.add(suffix);
    
    // Prove sortedness by cases
    assert(forall|i: int| 0 <= i < result.len() - 1 ==> result[i] <= result[i + 1]) by {
        assert(forall|i: int| 0 <= i < result.len() - 1 ==> {
            if i < prefix.len() - 1 {
                // Within prefix
                result[i] == prefix[i] && result[i + 1] == prefix[i + 1] && 
                prefix[i] <= prefix[i + 1]
            } else if i == prefix.len() - 1 && prefix.len() > 0 {
                // Transition from prefix to x
                result[i] == prefix[i] && result[i + 1] == x &&
                prefix[i] == s[i] && s[i] <= x
            } else if i == prefix.len() {
                // Transition from x to suffix
                result[i] == x && result[i + 1] == suffix[0] &&
                suffix[0] == s[pos] && x <= s[pos]
            } else {
                // Within suffix
                let suffix_idx = i - prefix.len() - 1;
                result[i] == suffix[suffix_idx] && result[i + 1] == suffix[suffix_idx + 1] &&
                suffix[suffix_idx] <= suffix[suffix_idx + 1]
            }
        });
    };
}

proof fn lemma_count_decomposition(s: Seq<int>, first: int)
    requires s.len() > 0 && s[0] == first
    ensures forall|x: int| s.subrange(1, s.len() as int).count(x) == s.count(x) - (if x == first { 1 } else { 0 })
{
    let rest = s.subrange(1, s.len() as int);
    assert(forall|x: int| {
        s.count(x) == (if s[0] == x { 1 } else { 0 }) + rest.count(x)
    });
    assert(forall|x: int| {
        rest.count(x) == s.count(x) - (if s[0] == x { 1 } else { 0 })
    });
    assert(forall|x: int| {
        rest.count(x) == s.count(x) - (if x == first { 1 } else { 0 })
    });
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
        
        // Chain the count equalities to prove contains_same_elements
        assert(forall|y: int| {
            // From lemma_count_decomposition: rest.count(y) == input.count(y) - (if y == first { 1 } else { 0 })
            // From recursive call: sorted_rest.count(y) == rest.count(y)
            // From insert_sorted: result.count(y) == sorted_rest.count(y) + (if y == first { 1 } else { 0 })
            // Therefore: result.count(y) == input.count(y)
            
            rest.count(y) == input.count(y) - (if y == first { 1 } else { 0 }) &&
            sorted_rest.count(y) == rest.count(y) &&
            result.count(y) == sorted_rest.count(y) + (if y == first { 1 } else { 0 })
        }) by {
            // This follows from the lemma and postconditions
        };
        
        assert(contains_same_elements(input, result));
        
        result
    }
}

}