// <vc-preamble>
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
spec fn extract_last_digit_spec(n: int) -> (ret:int) {
    n % 10
}
spec fn is_odd(n: int) -> (ret:bool) {
    (n % 2) != 0
}

spec fn is_valid_element_spec(n: int) -> (ret:bool) {
    &&& (n > 10)
    &&& is_odd(extract_first_digit_spec(n))
    &&& is_odd(extract_last_digit_spec(n))
}
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
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 4): fixed type annotation for integer literals */
proof fn lemma_special_filter_take_relationship(seq: Seq<i32>, i: int)
    requires
        0 <= i <= seq.len(),
    ensures
        special_filter_spec(seq.take(i)) == if i == 0 { 0 } else { special_filter_spec(seq.take(i - 1)) + if is_valid_element_spec(seq[i - 1] as int) { 1int } else { 0int } },
    decreases i,
{
    if i == 0 {
        assert(seq.take(0).len() == 0);
    } else {
        assert(seq.take(i) =~= seq.take(i - 1).push(seq[i - 1]));
        lemma_special_filter_push(seq.take(i - 1), seq[i - 1]);
    }
}

proof fn lemma_special_filter_push(seq: Seq<i32>, elem: i32)
    ensures
        special_filter_spec(seq.push(elem)) == special_filter_spec(seq) + if is_valid_element_spec(elem as int) { 1int } else { 0int },
    decreases seq.len(),
{
    if seq.len() == 0 {
        assert(seq.push(elem).drop_last() =~= seq);
        assert(seq.push(elem).last() == elem);
    } else {
        assert(seq.push(elem).drop_last() =~= seq);
        assert(seq.push(elem).last() == elem);
    }
}

proof fn lemma_take_full(seq: Seq<i32>)
    ensures seq.take(seq.len() as int) == seq,
{
}

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
    requires n >= 0,
    ensures ret == extract_last_digit_spec(n as int),
{
    n % 10
}

fn is_odd_impl(n: i32) -> (ret: bool)
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
        is_odd_impl(first) && is_odd_impl(last)
    } else {
        false
    }
}
// </vc-helpers>

// <vc-spec>
fn special_filter(numbers: &Vec<i32>) -> (count: usize)

    ensures
        count == special_filter_spec(numbers@),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 4): implementation unchanged, type fix was in helpers */
    let mut count: usize = 0;
    let mut i: usize = 0;
    
    while i < numbers.len()
        invariant
            0 <= i <= numbers.len(),
            count <= i,
            count == special_filter_spec(numbers@.take(i as int)) as usize,
            special_filter_spec(numbers@.take(i as int)) >= 0,
            special_filter_spec(numbers@.take(i as int)) <= i as int,
        decreases numbers.len() - i,
    {
        let n = numbers[i];
        let old_count = count;
        
        if n >= 0 && is_valid_element(n) {
            count = count + 1;
        }
        
        proof {
            lemma_special_filter_take_relationship(numbers@, (i + 1) as int);
            assert(numbers@.take((i + 1) as int) =~= numbers@.take(i as int).push(numbers@[i as int]));
            
            if n >= 0 && is_valid_element_spec(n as int) {
                assert(special_filter_spec(numbers@.take((i + 1) as int)) == special_filter_spec(numbers@.take(i as int)) + 1);
                assert(count == old_count + 1);
            } else {
                assert(special_filter_spec(numbers@.take((i + 1) as int)) == special_filter_spec(numbers@.take(i as int)));
                assert(count == old_count);
            }
        }
        
        i = i + 1;
    }
    
    proof {
        lemma_take_full(numbers@);
        assert(numbers@.take(numbers.len() as int) == numbers@);
    }
    
    count
}
// </vc-code>

}
fn main() {}