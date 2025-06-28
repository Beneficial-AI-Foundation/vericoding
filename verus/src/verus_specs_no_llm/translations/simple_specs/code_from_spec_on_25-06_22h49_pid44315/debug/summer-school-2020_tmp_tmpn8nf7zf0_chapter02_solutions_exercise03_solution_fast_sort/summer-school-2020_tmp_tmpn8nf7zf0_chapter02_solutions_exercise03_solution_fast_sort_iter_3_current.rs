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
        
        // Prove sortedness
        assert(forall|i: int| 0 <= i < (result.len() as int) - 1 ==> {
            if i < (sorted.len() as int) - 1 {
                result[i] == sorted[i] && result[i + 1] == sorted[i + 1]
            } else if i == (sorted.len() as int) - 1 {
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
        let result = prefix.add(seq![x]).add(suffix);
        
        // Prove properties
        lemma_insert_maintains_sorted(sorted, x, pos as int);
        
        result
    } else {
        // Continue searching for insertion point
        assert(sorted[pos as int] < x);
        insert_sorted_rec(sorted, x, pos + 1)
    }
}

proof fn lemma_subrange_sorted(s: Seq<int>, start: int, end: int)
    requires 
        IsSorted(s) &&
        0 <= start <= end <= s.len()
    ensures IsSorted(s.subrange(start, end))
{
    let sub = s.subrange(start, end);
    assert(forall|i: int| 0 <= i < (sub.len() as int) - 1 ==> {
        sub[i] == s[start + i] &&
        sub[i + 1] == s[start + i + 1] &&
        s[start + i] <= s[start + i + 1]
    });
}

proof fn lemma_insert_maintains_sorted(s: Seq<int>, x: int, pos: int)
    requires 
        IsSorted(s) &&
        0 <= pos <= s.len() &&
        (pos == 0 || s[pos - 1] <= x) &&
        (pos == s.len() || x <= s[pos])
    ensures 
        IsSorted(s.subrange(0, pos).add(seq![x]).add(s.subrange(pos, s.len() as int)))
{
    let prefix = s.subrange(0, pos);
    let suffix = s.subrange(pos, s.len() as int);
    let result = prefix.add(seq![x]).add(suffix);
    
    lemma_subrange_sorted(s, 0, pos);
    lemma_subrange_sorted(s, pos, s.len() as int);
    
    assert(forall|i: int| 0 <= i < (result.len() as int) - 1 ==> {
        if i < pos - 1 {
            result[i] == prefix[i] && result[i + 1] == prefix[i + 1]
        } else if i == pos - 1 && pos > 0 {
            result[i] == prefix[i] && result[i + 1] == x && prefix[i] <= x
        } else if i == pos {
            result[i] == x && result[i + 1] == suffix[0] && x <= suffix[0]
        } else {
            result[i] == suffix[i - pos - 1] && result[i + 1] == suffix[i - pos]
        }
    });
}

proof fn lemma_subrange_count(s: Seq<int>, start: int, end: int, x: int)
    requires 0 <= start <= end <= s.len()
    ensures s.subrange(start, end).count(x) <= s.count(x)
{
}

proof fn lemma_count_decomposition(s: Seq<int>, first: int)
    requires s.len() > 0
    ensures forall|x: int| s.subrange(1, s.len() as int).count(x) == s.count(x) - (if x == first { 1 } else { 0 })
{
}

fn fast_sort(input: Seq<int>) -> (output: Seq<int>)
    ensures SortSpec(input, output)
    decreases input.len()
{
    if input.len() == 0 {
        Seq::empty()
    } else {
        let first = input[0];
        let rest = input.subrange(1, input.len() as int);
        
        // Prove count property for rest
        lemma_count_decomposition(input, first);
        assert(forall|x: int| rest.count(x) == input.count(x) - (if x == first { 1 } else { 0 }));
        
        let sorted_rest = fast_sort(rest);
        
        // sorted_rest maintains the count relationship with rest
        assert(contains_same_elements(rest, sorted_rest));
        
        let result = insert_sorted(sorted_rest, first);
        
        // Prove that the final result satisfies the specification
        assert(forall|x: int| {
            result.count(x) == sorted_rest.count(x) + (if x == first { 1 } else { 0 }) &&
            sorted_rest.count(x) == rest.count(x) &&
            rest.count(x) == input.count(x) - (if x == first { 1 } else { 0 })
        } ==> result.count(x) == input.count(x));
        
        result
    }
}

}