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
        sorted.push(x)
    } else if sorted[pos as int] >= x {
        // Insert at current position
        let prefix = sorted.subrange(0, pos as int);
        let suffix = sorted.subrange(pos as int, sorted.len() as int);
        prefix.add(seq![x]).add(suffix)
    } else {
        // Continue searching for insertion point
        let prefix = sorted.subrange(0, (pos + 1) as int);
        let suffix = sorted.subrange((pos + 1) as int, sorted.len() as int);
        let inserted_suffix = insert_sorted_rec(suffix, x, 0);
        prefix.add(inserted_suffix)
    }
}

proof fn lemma_subrange_sorted(s: Seq<int>, start: int, end: int)
    requires 
        IsSorted(s) &&
        0 <= start <= end <= s.len()
    ensures IsSorted(s.subrange(start, end))
{
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
        let sorted_rest = fast_sort(rest);
        
        // Prove that the subrange maintains the element count property
        assert(forall|x: int| rest.count(x) == input.count(x) - (if x == first { 1 } else { 0 }));
        
        let result = insert_sorted(sorted_rest, first);
        
        // Prove that the final result satisfies the specification
        assert(forall|x: int| {
            result.count(x) == sorted_rest.count(x) + (if x == first { 1 } else { 0 }) &&
            sorted_rest.count(x) == rest.count(x) &&
            rest.count(x) == input.count(x) - (if x == first { 1 } else { 0 })
        });
        
        result
    }
}

}