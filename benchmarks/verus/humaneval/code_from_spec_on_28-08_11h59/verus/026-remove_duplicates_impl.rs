use vstd::prelude::*;

verus! {

spec fn count_frequency_spec(seq: Seq<i64>, key: i64) -> (result:int)
    decreases seq.len(),
{
    if seq.len() == 0 {
        0
    } else {
        count_frequency_spec(seq.drop_last(), key) + if (seq.last() == key) {
            1 as int
        } else {
            0 as int
        }
    }
}
// pure-end

// <vc-helpers>
fn count_frequency(elements: &Vec<i64>, key: i64) -> (frequency: usize)
    // post-conditions-start
    ensures
        count_frequency_spec(elements@, key) == frequency,
    // post-conditions-end
{
    // impl-start
    let ghost elements_length = elements.len();
    let mut counter = 0;
    let mut index = 0;
    while index < elements.len()
        // invariants-start
        invariant
            0 <= index <= elements.len(),
            0 <= counter <= index,
            count_frequency_spec(elements@.subrange(0, index as int), key) == counter,
        // invariants-end
        decreases elements.len() - index,
    {
        if (elements[index] == key) {
            counter += 1;
        }
        index += 1;
        // assert-start
        assert(elements@.subrange(0, index - 1 as int) == elements@.subrange(
            0,
            index as int,
        ).drop_last());
        // assert-end
    }
    // assert-start
    assert(elements@ == elements@.subrange(0, elements_length as int));
    // assert-end
    counter
    // impl-end
}

proof fn lemma_filter_preserve_order(s: Seq<i64>, pred: spec_fn(i64) -> bool, i: int, j: int)
    requires
        0 <= i < j < s.len(),
        pred(s[i]),
        pred(s[j]),
    ensures
        exists |fi: int, fj: int| 0 <= fi < fj < s.filter(pred).len() && s.filter(pred)[fi] == s[i] && s.filter(pred)[fj] == s[j]
{
    let filtered = s.filter(pred);
    assert(filtered.contains(s[i]));
    assert(filtered.contains(s[j]));
    
    let mut fi: int = 0;
    while fi < filtered.len()
        invariant
            0 <= fi <= filtered.len(),
        decreases filtered.len() - fi,
    {
        if filtered[fi] == s[i] {
            break;
        }
        fi = fi + 1;
    }
    
    let mut fj = fi + 1;
    while fj < filtered.len()
        invariant
            fi < fj <= filtered.len(),
        decreases filtered.len() - fj,
    {
        if filtered[fj] == s[j] {
            break;
        }
        fj = fj + 1;
    }
    
    assert(0 <= fi < fj < filtered.len());
    assert(filtered[fi] == s[i] && filtered[fj] == s[j]);
}

proof fn lemma_filter_membership(s: Seq<i64>, pred: spec_fn(i64) -> bool, x: i64)
    requires
        s.contains(x),
        pred(x),
    ensures
        s.filter(pred).contains(x)
{
    assert(s.filter(pred).contains(x));
}

proof fn lemma_count_frequency_filter(numbers: Seq<i64>, x: i64)
    ensures
        numbers.filter(|y: i64| count_frequency_spec(numbers, y) == 1).contains(x) <==> 
        (numbers.contains(x) && count_frequency_spec(numbers, x) == 1)
{
    if numbers.filter(|y: i64| count_frequency_spec(numbers, y) == 1).contains(x) {
        assert(count_frequency_spec(numbers, x) == 1);
        assert(numbers.contains(x));
    }
    
    if numbers.contains(x) && count_frequency_spec(numbers, x) == 1 {
        assert(numbers.filter(|y: i64| count_frequency_spec(numbers, y) == 1).contains(x));
    }
}

proof fn lemma_subrange_filter(s: Seq<i64>, pred: spec_fn(i64) -> bool, i: int, x: i64)
    requires
        0 <= i <= s.len(),
    ensures
        s.subrange(0, i).push(x).filter(pred) == s.subrange(0, i).filter(pred) + if pred(x) { seq![x] } else { seq![] }
{
}
// </vc-helpers>

// <vc-spec>
fn remove_duplicates(numbers: &Vec<i64>) -> (unique_numbers: Vec<i64>)
    // post-conditions-start
    ensures
        unique_numbers@ == numbers@.filter(|x: i64| count_frequency_spec(numbers@, x) == 1),
    // post-conditions-end
// </vc-spec>
// <vc-code>
{
    let mut result = Vec::new();
    let mut i = 0;
    
    while i < numbers.len()
        invariant
            0 <= i <= numbers.len(),
            result@ == numbers@.subrange(0, i as int).filter(|x: i64| count_frequency_spec(numbers@, x) == 1),
        decreases numbers.len() - i,
    {
        let current = numbers[i];
        let freq = count_frequency(numbers, current);
        
        if freq == 1 {
            result.push(current);
        }
        
        i += 1;
        
        proof {
            assert(numbers@.subrange(0, i as int) == numbers@.subrange(0, (i-1) as int).push(current));
            lemma_subrange_filter(numbers@.subrange(0, (i-1) as int), |x: i64| count_frequency_spec(numbers@, x) == 1, (i-1) as int, current);
        }
    }
    
    proof {
        assert(numbers@.subrange(0, numbers.len() as int) == numbers@);
    }
    
    result
}
// </vc-code>

} // verus!
fn main() {}