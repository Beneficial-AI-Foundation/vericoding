use vstd::prelude::*;

verus! {

spec fn count_frequency_rcr(seq: Seq<i32>, key: i32) -> (result: int)
    decreases seq.len(),
{
    if seq.len() == 0 {
        0
    } else {
        count_frequency_rcr(seq.drop_last(), key) + if (seq.last() == key) {
            1 as int
        } else {
            0 as int
        }
    }
}
// pure-end

// <vc-helpers>
fn count_frequency(arr: &Vec<i32>, key: i32) -> (frequency: usize)
    ensures
        count_frequency_rcr(arr@, key) == frequency,
{
    let mut index = 0;
    let mut counter = 0;
    while index < arr.len()
        invariant
            0 <= index <= arr.len(),
            0 <= counter <= index,
            count_frequency_rcr(arr@.subrange(0, index as int), key) == counter,
        decreases arr.len() - index,
    {
        if arr[index] == key {
            counter += 1;
        }
        index += 1;
    }
    counter
}

proof fn lemma_filter_count_frequency(arr: Seq<i32>, key: i32, index: int)
    requires
        0 <= index <= arr.len(),
    ensures
        count_frequency_rcr(arr.subrange(0, index), key) == arr.subrange(0, index).filter(|x: i32| x == key).len(),
    decreases index,
{
    if index == 0 {
        assert(arr.subrange(0, 0) == Seq::<i32>::empty());
        assert(Seq::<i32>::empty().filter(|x: i32| x == key) == Seq::<i32>::empty());
    } else {
        lemma_filter_count_frequency(arr, key, index - 1);
        assert(arr.subrange(0, index).drop_last() == arr.subrange(0, index - 1));
        if arr.subrange(0, index).last() == key {
            assert(arr.subrange(0, index).filter(|x: i32| x == key) == arr.subrange(0, index - 1).filter(|x: i32| x == key).push(key));
            assert(arr.subrange(0, index).filter(|x: i32| x == key).len() == arr.subrange(0, index - 1).filter(|x: i32| x == key).len() + 1);
        } else {
            assert(arr.subrange(0, index).filter(|x: i32| x == key) == arr.subrange(0, index - 1).filter(|x: i32| x == key));
            assert(arr.subrange(0, index).filter(|x: i32| x == key).len() == arr.subrange(0, index - 1).filter(|x: i32| x == key).len());
        }
    }
}

proof fn lemma_filter_unique_up_to(arr: Seq<i32>, i: int)
    requires
        0 <= i <= arr.len(),
    ensures
        arr.subrange(0, i).filter(|x: i32| count_frequency_rcr(arr, x) == 1) == arr.subrange(0, i).filter(|x: i32| count_frequency_rcr(arr.subrange(0, i), x) == 1),
    decreases i,
{
    if i == 0 {
        assert(arr.subrange(0, 0) == Seq::<i32>::empty());
    } else {
        lemma_filter_unique_up_to(arr, i - 1);
        let current = arr.subrange(0, i).last();
        assert(arr.subrange(0, i).drop_last() == arr.subrange(0, i - 1));
        if count_frequency_rcr(arr.subrange(0, i), current) == 1 {
            assert(count_frequency_rcr(arr, current) == 1);
        } else {
            assert(count_frequency_rcr(arr, current) > 1);
        }
    }
}
// </vc-helpers>

// <vc-spec>
fn remove_duplicates(arr: &Vec<i32>) -> (unique_arr: Vec<i32>)
    // post-conditions-start
    ensures
        unique_arr@ == arr@.filter(|x: i32| count_frequency_rcr(arr@, x) == 1),
    // post-conditions-end
// </vc-spec>

// <vc-code>
{
    let mut result = Vec::new();
    let mut i = 0;

    while i < arr.len()
        invariant
            0 <= i <= arr.len(),
            result@ == arr@.subrange(0, i as int).filter(|x: i32| count_frequency_rcr(arr@, x) == 1),
        decreases arr.len() - i,
    {
        let current = arr[i];
        let freq = count_frequency(arr, current);
        if freq == 1 {
            result.push(current);
            proof {
                lemma_filter_unique_up_to(arr@, i as int + 1);
            }
        } else {
            proof {
                lemma_filter_unique_up_to(arr@, i as int + 1);
            }
        }
        i += 1;
    }

    result
}
// </vc-code>

} // verus!

fn main() {}