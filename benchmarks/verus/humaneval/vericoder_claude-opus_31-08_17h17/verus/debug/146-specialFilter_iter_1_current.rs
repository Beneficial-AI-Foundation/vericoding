use vstd::prelude::*;

verus! {

spec fn extract_first_digit_spec(n: int) -> (ret:int)
    decreases n,
{
    if n < 10 {
        n
    } else {
        extract_first_digit_spec(n / 10)
    }
}
// pure-end
spec fn extract_last_digit_spec(n: int) -> (ret:int) {
    n % 10
}
// pure-end
spec fn is_odd(n: int) -> (ret:bool) {
    (n % 2) != 0
}
// pure-end
// pure-end


spec fn is_valid_element_spec(n: int) -> (ret:bool) {
    &&& (n > 10)
    &&& is_odd(extract_first_digit_spec(n))
    &&& is_odd(extract_last_digit_spec(n))
}
// pure-end
spec fn special_filter_spec(seq: Seq<i32>) -> (ret:int)
    decreases seq.len(),
{
    if seq.len() == 0 {
        0
    } else {
        special_filter_spec(seq.drop_last()) + if (is_valid_element_spec(seq.last() as int)) {
            1 as int
        } else {
            0 as int
        }
    }
}
// pure-end

// <vc-helpers>
fn extract_first_digit(n: i32) -> (ret: i32)
    requires n >= 0,
    ensures ret == extract_first_digit_spec(n as int),
    decreases n,
{
    if n < 10 {
        n
    } else {
        extract_first_digit(n / 10)
    }
}

fn extract_last_digit(n: i32) -> (ret: i32)
    ensures ret == extract_last_digit_spec(n as int),
{
    n % 10
}

fn is_odd_fn(n: i32) -> (ret: bool)
    ensures ret == is_odd(n as int),
{
    (n % 2) != 0
}

fn is_valid_element(n: i32) -> (ret: bool)
    requires n >= 0,
    ensures ret == is_valid_element_spec(n as int),
{
    if n > 10 {
        let first = extract_first_digit(n);
        let last = extract_last_digit(n);
        is_odd_fn(first) && is_odd_fn(last)
    } else {
        false
    }
}

proof fn special_filter_spec_empty()
    ensures special_filter_spec(Seq::<i32>::empty()) == 0,
{
    assert(Seq::<i32>::empty().len() == 0);
}

proof fn special_filter_spec_push(s: Seq<i32>, x: i32)
    ensures special_filter_spec(s.push(x)) == special_filter_spec(s) + if is_valid_element_spec(x as int) { 1 } else { 0 },
    decreases s.len(),
{
    reveal_with_fuel(special_filter_spec, 2);
    assert(s.push(x).drop_last() =~= s);
    assert(s.push(x).last() == x);
}
// </vc-helpers>

// <vc-spec>
fn special_filter(numbers: &Vec<i32>) -> (count: usize)
    // post-conditions-start
    ensures
        count == special_filter_spec(numbers@),
    // post-conditions-end
// </vc-spec>
// <vc-code>
{
    let mut count: usize = 0;
    let mut i: usize = 0;
    
    while i < numbers.len()
        invariant
            0 <= i <= numbers.len(),
            count == special_filter_spec(numbers@.take(i as int)) as usize,
    {
        let elem = numbers[i];
        
        assert(numbers@.take(i as int).push(elem) =~= numbers@.take((i + 1) as int)) by {
            assert forall |j: int| 0 <= j < i + 1 implies 
                #[trigger] numbers@.take((i + 1) as int)[j] == numbers@.take(i as int).push(elem)[j] by {
                if j < i {
                    assert(numbers@.take((i + 1) as int)[j] == numbers@[j]);
                    assert(numbers@.take(i as int)[j] == numbers@[j]);
                    assert(numbers@.take(i as int).push(elem)[j] == numbers@.take(i as int)[j]);
                } else {
                    assert(j == i);
                    assert(numbers@.take((i + 1) as int)[j] == numbers@[i]);
                    assert(numbers@[i] == elem);
                    assert(numbers@.take(i as int).push(elem)[j] == elem);
                }
            }
        }
        
        if elem >= 0 && is_valid_element(elem) {
            proof {
                special_filter_spec_push(numbers@.take(i as int), elem);
            }
            count = count + 1;
        } else {
            proof {
                special_filter_spec_push(numbers@.take(i as int), elem);
                if elem < 0 {
                    assert(!is_valid_element_spec(elem as int));
                }
            }
        }
        
        i = i + 1;
    }
    
    assert(numbers@.take(numbers.len() as int) =~= numbers@);
    count
}
// </vc-code>

} // verus!
fn main() {}