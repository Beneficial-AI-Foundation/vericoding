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
        sorted.push(x)
    } else if sorted[pos as int] >= x {
        seq![x].add(sorted)
    } else {
        seq![sorted[pos as int]].add(insert_sorted_rec(sorted.subrange(1, sorted.len() as int), x, pos))
    }
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
        insert_sorted(sorted_rest, first)
    }
}

}