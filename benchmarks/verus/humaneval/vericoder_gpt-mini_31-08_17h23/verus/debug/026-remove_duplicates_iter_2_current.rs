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
proof fn count_frequency_spec_eq_filter(seq: Seq<i64>, key: i64)
    decreases seq.len()
{
    if seq.len() == 0 {
        assert(count_frequency_spec(seq, key) == 0);
        assert(seq.filter(|y: i64| y == key).len() == 0);
    } else {
        let tail = seq.drop_last();
        count_frequency_spec_eq_filter(tail, key);
        assert(count_frequency_spec(seq, key) == count_frequency_spec(tail, key) + if seq.last() == key { 1 } else { 0 });
        assert(seq.filter(|y: i64| y == key).len() == tail.filter(|y: i64| y == key).len() + if seq.last() == key { 1 } else { 0 });
        assert(tail.filter(|y: i64| y == key).len() == count_frequency_spec(tail, key));
        assert(seq.filter(|y: i64| y == key).len() == count_frequency_spec(seq, key));
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
    let n: usize = numbers.len();
    let mut unique_numbers: Vec<i64> = Vec::new();

    let mut i: usize = 0;
    while i < n
        invariant i <= n
        invariant unique_numbers@ == numbers@.slice(0, i).filter(|x| count_frequency_spec(numbers@, x) == 1)
        decreases n - i
    {
        let xi: i64 = numbers.get(i);

        let mut j: usize = 0;
        let mut found: bool = false;
        while j < n && !found
            invariant j <= n
            invariant found == (exists |k: int| 0 <= k && k < j as int && k != i as int && numbers@.index(k) == xi)
            decreases n - j
        {
            if j != i && numbers.get(j) == xi {
                found = true;
            }
            j = j + 1;
        }

        proof {
            if found {
                // from invariant and j <= n we get existence within 0..n
                assert(exists |k: int| 0 <= k && k < n as int && k != i as int && numbers@.index(k) == xi);
                // hence frequency >= 2, so not equal to 1
                count_frequency_spec_eq_filter(numbers@, xi);
                assert(!(count_frequency_spec(numbers@, xi) == 1));
            } else {
                // loop terminated with !found, so by loop condition and invariant j <= n we have j == n
                assert(j == n);
                // from invariant and found == false we get that no k < j (== n) satisfies the exists predicate
                assert(! (exists |k: int| 0 <= k && k < j as int && k != i as int && numbers@.index(k) == xi));
                // hence for all k < n, not(k != i && numbers@.index(k) == xi), equivalently if numbers@[k]==xi then k==i
                assert(forall |k: int| 0 <= k && k < n as int ==> (numbers@.index(k) == xi ==> k == i as int));
                // therefore xi occurs exactly once in numbers@
                count_frequency_spec_eq_filter(numbers@, xi);
                assert(count_frequency_spec(numbers@, xi) == 1);
            }
        }

        if !found {
            unique_numbers.push(xi);
        }

        i = i + 1;
    }

    unique_numbers
}
// </vc-code>

} // verus!
fn main() {}