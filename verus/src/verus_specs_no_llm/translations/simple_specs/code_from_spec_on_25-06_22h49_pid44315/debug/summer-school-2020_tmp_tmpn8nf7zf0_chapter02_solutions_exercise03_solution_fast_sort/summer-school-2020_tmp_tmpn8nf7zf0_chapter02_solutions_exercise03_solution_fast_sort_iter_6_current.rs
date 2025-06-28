use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn count(s: Seq<int>, x: int) -> nat 
    decreases s.len()
{
    if s.len() == 0 {
        0
    } else {
        count(s.drop_first(), x) + (if s.first() == x { 1 } else { 0 })
    }
}

spec fn IsSorted(s: Seq<int>) -> bool {
    forall|i: int| 0 <= i < (s.len() as int) - 1 ==> s[i] <= s[i + 1]
}

spec fn contains_same_elements(s1: Seq<int>, s2: Seq<int>) -> bool {
    forall|x: int| count(s1, x) == count(s2, x)
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
        forall|y: int| count(result, y) == count(sorted, y) + (if y == x { 1 } else { 0 })
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
        forall|y: int| count(result, y) == count(sorted, y) + (if y == x { 1 } else { 0 })
    decreases sorted.len() - pos
{
    if pos == sorted.len() {
        let result = sorted.push(x);
        
        assert(forall|i: int| 0 <= i < sorted.len() ==> sorted[i] <= x);
        
        proof {
            lemma_count_push(sorted, x);
        }
        
        result
    } else if sorted[pos as int] >= x {
        let prefix = sorted.subrange(0, pos as int);
        let suffix = sorted.subrange(pos as int, sorted.len() as int);
        let middle = seq![x];
        let temp = prefix.add(middle);
        let result = temp.add(suffix);
        
        proof {
            lemma_insert_maintains_sorted_at_pos(sorted, x, pos as int);
            lemma_count_insert_at_pos(sorted, x, pos as int);
        }
        
        result
    } else {
        assert(sorted[pos as int] < x);
        assert(forall|i: int| 0 <= i < pos + 1 ==> sorted[i] <= x) by {
            assert(forall|i: int| 0 <= i < pos ==> sorted[i] <= x);
            assert(sorted[pos as int] < x);
            assert(sorted[pos as int] <= x);
        };
        insert_sorted_rec(sorted, x, pos + 1)
    }
}

proof fn lemma_count_push(s: Seq<int>, x: int)
    ensures forall|y: int| count(s.push(x), y) == count(s, y) + (if y == x { 1 } else { 0 })
{
    let result = s.push(x);
    assert(result.len() == s.len() + 1);
    assert(result[s.len() as int] == x);
    assert(forall|i: int| 0 <= i < s.len() ==> result[i] == s[i]);
    
    assert(forall|y: int| count(result, y) == count(s, y) + (if y == x { 1 } else { 0 })) by {
        lemma_count_push_helper(s, x);
    }
}

proof fn lemma_count_push_helper(s: Seq<int>, x: int)
    ensures forall|y: int| count(s.push(x), y) == count(s, y) + (if y == x { 1 } else { 0 })
    decreases s.len()
{
    if s.len() == 0 {
        let result = s.push(x);
        assert(result =~= seq![x]);
        assert(forall|y: int| count(result, y) == (if y == x { 1 } else { 0 }));
        assert(forall|y: int| count(s, y) == 0);
    } else {
        let result = s.push(x);
        assert(result.first() == s.first());
        assert(result.drop_first() =~= s.drop_first().push(x));
        lemma_count_push_helper(s.drop_first(), x);
    }
}

proof fn lemma_count_insert_at_pos(s: Seq<int>, x: int, pos: int)
    requires 0 <= pos <= s.len()
    ensures {
        let prefix = s.subrange(0, pos);
        let suffix = s.subrange(pos, s.len() as int);
        let result = prefix.add(seq![x]).add(suffix);
        forall|y: int| count(result, y) == count(s, y) + (if y == x { 1 } else { 0 })
    }
{
    let prefix = s.subrange(0, pos);
    let suffix = s.subrange(pos, s.len() as int);
    let middle = seq![x];
    let temp = prefix.add(middle);
    let result = temp.add(suffix);
    
    lemma_count_add(prefix, middle);
    lemma_count_add(temp, suffix);
    lemma_count_subrange_split(s, pos);
}

proof fn lemma_count_add(s1: Seq<int>, s2: Seq<int>)
    ensures forall|y: int| count(s1.add(s2), y) == count(s1, y) + count(s2, y)
    decreases s1.len()
{
    if s1.len() == 0 {
        assert(s1.add(s2) =~= s2);
    } else {
        let result = s1.add(s2);
        assert(result.first() == s1.first());
        assert(result.drop_first() =~= s1.drop_first().add(s2));
        lemma_count_add(s1.drop_first(), s2);
    }
}

proof fn lemma_count_subrange_split(s: Seq<int>, pos: int)
    requires 0 <= pos <= s.len()
    ensures {
        let prefix = s.subrange(0, pos);
        let suffix = s.subrange(pos, s.len() as int);
        forall|y: int| count(s, y) == count(prefix, y) + count(suffix, y)
    }
    decreases s.len()
{
    if pos == 0 {
        let prefix = s.subrange(0, 0);
        let suffix = s.subrange(0, s.len() as int);
        assert(prefix.len() == 0);
        assert(suffix =~= s);
        assert(forall|y: int| count(prefix, y) == 0);
    } else if pos == s.len() {
        let prefix = s.subrange(0, s.len() as int);
        let suffix = s.subrange(s.len() as int, s.len() as int);
        assert(prefix =~= s);
        assert(suffix.len() == 0);
        assert(forall|y: int| count(suffix, y) == 0);
    } else {
        let prefix = s.subrange(0, pos);
        let suffix = s.subrange(pos, s.len() as int);
        lemma_count_subrange_split(s.drop_first(), pos - 1);
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
    
    lemma_subrange_sorted(s, 0, pos);
    lemma_subrange_sorted(s, pos, s.len() as int);
}

proof fn lemma_subrange_sorted(s: Seq<int>, start: int, end: int)
    requires IsSorted(s) && 0 <= start <= end <= s.len()
    ensures IsSorted(s.subrange(start, end))
{
}

proof fn lemma_count_decomposition(s: Seq<int>, first: int)
    requires s.len() > 0 && s[0] == first
    ensures forall|x: int| count(s.subrange(1, s.len() as int), x) == count(s, x) - (if x == first { 1 } else { 0 })
{
    let rest = s.subrange(1, s.len() as int);
    assert(s.drop_first() =~= rest);
    lemma_count_first_drop(s, first);
}

proof fn lemma_count_first_drop(s: Seq<int>, first: int)
    requires s.len() > 0 && s.first() == first
    ensures forall|x: int| count(s.drop_first(), x) == count(s, x) - (if x == first { 1 } else { 0 })
{
    // This follows from the definition of count
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
        
        proof {
            lemma_count_decomposition(input, first);
        }
        
        let sorted_rest = fast_sort(rest);
        let result = insert_sorted(sorted_rest, first);
        
        proof {
            lemma_fast_sort_correctness(input, first, rest, sorted_rest, result);
        }
        
        result
    }
}

proof fn lemma_fast_sort_correctness(
    input: Seq<int>, 
    first: int, 
    rest: Seq<int>, 
    sorted_rest: Seq<int>, 
    result: Seq<int>
)
    requires 
        input.len() > 0 &&
        first == input[0] &&
        rest =~= input.subrange(1, input.len() as int) &&
        contains_same_elements(rest, sorted_rest) &&
        IsSorted(result) &&
        forall|y: int| count(result, y) == count(sorted_rest, y) + (if y == first { 1 } else { 0 }) &&
        forall|x: int| count(rest, x) == count(input, x) - (if x == first { 1 } else { 0 })
    ensures contains_same_elements(input, result)
{
    assert(forall|y: int| {
        count(result, y) == count(sorted_rest, y) + (if y == first { 1 } else { 0 }) &&
        count(sorted_rest, y) == count(rest, y) &&
        count(rest, y) == count(input, y) - (if y == first { 1 } else { 0 })
    });
    
    assert(forall|y: int| count(result, y) == count(input, y));
}

}