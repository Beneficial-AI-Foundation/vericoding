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

fn count_frequency(elements: &Vec<i64>, key: i64) -> (frequency: usize)
    // post-conditions-start
    ensures
        count_frequency_spec(elements@, key) == frequency,
    // post-conditions-end
{
    let mut count = 0;
    let mut i = 0;
    
    /* code modified by LLM (iteration 4): added helper lemma call and fixed invariant maintenance */
    while i < elements.len()
        invariant
            i <= elements.len(),
            count <= i,
            count == count_frequency_spec(elements@.subrange(0, i as int), key),
        decreases elements.len() - i,
    {
        if elements[i] == key {
            assert(count < elements.len());
            count = count + 1;
        }
        
        /* code modified by LLM (iteration 4): moved ghost operations into proof block */
        proof {
            assert(elements@.subrange(0, (i + 1) as int) == elements@.subrange(0, i as int).push(elements@[i as int]));
            lemma_count_frequency_extend(elements@.subrange(0, i as int), elements@[i as int], key);
        }
        
        i = i + 1;
    }
    
    assert(elements@.subrange(0, elements.len() as int) == elements@);
    count
}

/* code modified by LLM (iteration 4): added helper lemma to prove count_frequency extension property */
proof fn lemma_count_frequency_extend(seq: Seq<i64>, elem: i64, key: i64)
    ensures count_frequency_spec(seq.push(elem), key) == count_frequency_spec(seq, key) + if elem == key { 1 } else { 0 }
{
    if seq.len() == 0 {
        assert(seq.push(elem) == seq![elem]);
        assert(count_frequency_spec(seq![elem], key) == if elem == key { 1 } else { 0 });
    } else {
        let seq_extended = seq.push(elem);
        assert(seq_extended.drop_last() == seq);
        assert(seq_extended.last() == elem);
    }
}

fn remove_duplicates(numbers: &Vec<i64>) -> (unique_numbers: Vec<i64>)
    // post-conditions-start
    ensures
        unique_numbers@ == numbers@.filter(|x: i64| count_frequency_spec(numbers@, x) == 1),
    // post-conditions-end
{
    let mut result = Vec::new();
    let mut i = 0;
    
    /* code modified by LLM (iteration 4): simplified invariant maintenance with helper lemma */
    while i < numbers.len()
        invariant
            i <= numbers.len(),
            result@ == numbers@.subrange(0, i as int).filter(|x: i64| count_frequency_spec(numbers@, x) == 1),
        decreases numbers.len() - i,
    {
        let current = numbers[i];
        let freq = count_frequency(numbers, current);
        
        assert(freq == count_frequency_spec(numbers@, current));
        
        if freq == 1 {
            result.push(current);
            assert(count_frequency_spec(numbers@, current) == 1);
        }
        
        /* code modified by LLM (iteration 4): moved ghost operations into proof block */
        proof {
            lemma_filter_extend(numbers@.subrange(0, i as int), current, |x: i64| count_frequency_spec(numbers@, x) == 1);
            assert(numbers@.subrange(0, (i + 1) as int) == numbers@.subrange(0, i as int).push(current));
        }
        
        i = i + 1;
    }
    
    assert(numbers@.subrange(0, numbers.len() as int) == numbers@);
    result
}

/* code modified by LLM (iteration 4): added helper lemma for filter extension */
proof fn lemma_filter_extend<T>(seq: Seq<T>, elem: T, pred: spec_fn(T) -> bool)
    ensures seq.push(elem).filter(pred) == 
        if pred(elem) { seq.filter(pred).push(elem) } else { seq.filter(pred) }
{
    let extended = seq.push(elem);
    if pred(elem) {
        assert(extended.filter(pred) == seq.filter(pred).push(elem));
    } else {
        assert(extended.filter(pred) == seq.filter(pred));
    }
}

} // verus!
fn main() {}