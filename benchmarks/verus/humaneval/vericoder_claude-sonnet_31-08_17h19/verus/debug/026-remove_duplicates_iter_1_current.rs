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
proof fn count_frequency_spec_monotonic(seq: Seq<i64>, key: i64, n: nat)
    requires n <= seq.len()
    ensures count_frequency_spec(seq.subrange(0, n as int), key) <= count_frequency_spec(seq, key)
    decreases seq.len() - n
{
    if n == seq.len() {
        assert(seq.subrange(0, n as int) == seq);
    } else {
        count_frequency_spec_monotonic(seq, key, n + 1);
    }
}

proof fn count_frequency_spec_take_drop(seq: Seq<i64>, key: i64, n: nat)
    requires n <= seq.len()
    ensures count_frequency_spec(seq.subrange(0, n as int), key) + count_frequency_spec(seq.subrange(n as int, seq.len() as int), key) == count_frequency_spec(seq, key)
    decreases seq.len() - n
{
    if n == seq.len() {
        assert(seq.subrange(n as int, seq.len() as int).len() == 0);
    } else {
        count_frequency_spec_take_drop(seq, key, n + 1);
    }
}

proof fn count_frequency_spec_append(s1: Seq<i64>, s2: Seq<i64>, key: i64)
    ensures count_frequency_spec(s1 + s2, key) == count_frequency_spec(s1, key) + count_frequency_spec(s2, key)
    decreases s2.len()
{
    if s2.len() == 0 {
        assert(s1 + s2 == s1);
    } else {
        let s2_without_last = s2.drop_last();
        count_frequency_spec_append(s1, s2_without_last, key);
        assert((s1 + s2).drop_last() == s1 + s2_without_last);
        assert((s1 + s2).last() == s2.last());
    }
}

proof fn count_frequency_spec_push(seq: Seq<i64>, val: i64, key: i64)
    ensures count_frequency_spec(seq.push(val), key) == count_frequency_spec(seq, key) + if val == key { 1 } else { 0 }
{
    assert(seq.push(val) == seq + seq![val]);
    count_frequency_spec_append(seq, seq![val], key);
}

spec fn count_frequency_iter(seq: Seq<i64>, key: i64, pos: nat) -> int
    decreases pos
{
    if pos == 0 {
        0
    } else {
        count_frequency_iter(seq, key, pos - 1) + if seq[pos - 1] == key { 1 } else { 0 }
    }
}

proof fn count_frequency_equiv(seq: Seq<i64>, key: i64)
    ensures count_frequency_spec(seq, key) == count_frequency_iter(seq, key, seq.len())
    decreases seq.len()
{
    if seq.len() == 0 {
    } else {
        let shorter = seq.drop_last();
        count_frequency_equiv(shorter, key);
        assert(count_frequency_iter(seq, key, seq.len()) == 
               count_frequency_iter(shorter, key, shorter.len()) + 
               if seq[seq.len() - 1] == key { 1 } else { 0 });
        assert(seq[seq.len() - 1] == seq.last());
    }
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
    let mut unique_numbers: Vec<i64> = Vec::new();
    let mut i: usize = 0;
    
    while i < numbers.len()
        invariant
            i <= numbers.len(),
            unique_numbers@ == numbers@.subrange(0, i as int).filter(|x: i64| count_frequency_spec(numbers@, x) == 1),
    {
        let current = numbers[i];
        
        // Count frequency of current element
        let mut count = 0;
        let mut j = 0;
        
        while j < numbers.len()
            invariant
                j <= numbers.len(),
                count == count_frequency_iter(numbers@, current, j),
        {
            if numbers[j] == current {
                count = count + 1;
            }
            j = j + 1;
        }
        
        proof {
            count_frequency_equiv(numbers@, current);
        }
        
        if count == 1 {
            unique_numbers.push(current);
        }
        
        i = i + 1;
    }
    
    unique_numbers
}
// </vc-code>

} // verus!
fn main() {}