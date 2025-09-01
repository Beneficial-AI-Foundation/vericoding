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
// No helpers needed for this proof.
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
    // impl-start
    let mut unique_numbers: Vec<i64> = Vec::new();
    let n: usize = numbers.len();
    let mut i: usize = 0;
    while i < n
        invariant i <= n
        invariant unique_numbers@ == numbers@.slice(0, i).filter(|x: i64| count_frequency_spec(numbers@, x) == 1)
    {
        let key: i64 = numbers.get(i);
        // relate runtime key to spec sequence element
        assert(key == numbers@[@i]);

        // count occurrences of key in numbers by scanning whole array
        let mut cnt: int = 0;
        let mut j: usize = 0;
        while j < n
            invariant j <= n
            invariant cnt == count_frequency_spec(numbers@.slice(0, j), key)
        {
            let vj: i64 = numbers.get(j);
            assert(vj == numbers@[@j]);
            if vj == key {
                cnt = cnt + 1;
            }
            j = j + 1;
        }
        // now j == n, so cnt == count_frequency_spec(numbers@.slice(0,n), key) == count_frequency_spec(numbers@, key)
        assert(numbers@.slice(0, n) == numbers@);
        assert(cnt == count_frequency_spec(numbers@, key));

        if cnt == 1 {
            unique_numbers.push(key);
        }

        i = i + 1;
    }
    // at loop exit i == n, so by invariant unique_numbers@ == numbers@.slice(0,n).filter(...) == numbers@.filter(...)
    assert(numbers@.slice(0, n) == numbers@);
    assert(unique_numbers@ == numbers@.filter(|x: i64| count_frequency_spec(numbers@, x) == 1));
    unique_numbers
    // impl-end
}
// </vc-code>

} // verus!
fn main() {}