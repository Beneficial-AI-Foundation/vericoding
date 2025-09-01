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
proof fn lemma_special_filter_spec_append_one(seq: Seq<i32>, element: i32)
    ensures special_filter_spec(seq.push(element)) == special_filter_spec(seq) + if (is_valid_element_spec(element as int)) { 1 as int } else { 0 as int }
    decreases seq.len()
{
    if seq.len() == 0 {
        assert(seq.push(element).drop_last() =~= seq);
        assert(seq.push(element).last() == element);
    } else {
        let seq_without_last = seq.drop_last();
        let last_elem = seq.last();
        let new_seq = seq.push(element);
        
        assert(new_seq.drop_last() =~= seq);
        assert(new_seq.last() == element);
        
        lemma_special_filter_spec_append_one(seq_without_last, last_elem);
    }
}

proof fn lemma_special_filter_spec_subrange(seq: Seq<i32>, i: nat)
    requires i <= seq.len()
    ensures special_filter_spec(seq.subrange(0, i as int)) == 
        if i == 0 { 0 } else { 
            special_filter_spec(seq.subrange(0, i as int - 1)) + 
            if (is_valid_element_spec(seq[i as int - 1] as int)) { 1 as int } else { 0 as int }
        }
    decreases i
{
    if i == 0 {
        assert(seq.subrange(0, 0).len() == 0);
    } else {
        let sub_seq = seq.subrange(0, i as int);
        let sub_seq_prev = seq.subrange(0, i as int - 1);
        
        assert(sub_seq =~= sub_seq_prev.push(seq[i as int - 1]));
        lemma_special_filter_spec_append_one(sub_seq_prev, seq[i as int - 1]);
    }
}

proof fn lemma_extract_first_digit_properties(n: int)
    requires n > 10
    ensures extract_first_digit_spec(n) >= 1 && extract_first_digit_spec(n) <= 9
    decreases n
{
    if n / 10 < 10 {
        assert(extract_first_digit_spec(n) == n / 10);
        assert(n / 10 >= 1);
        assert(n / 10 <= 9);
    } else {
        lemma_extract_first_digit_properties(n / 10);
    }
}

proof fn lemma_extract_first_digit_correctness(temp: i32, n: i32)
    requires temp > 0 && temp < 10 && n > 10
    requires extract_first_digit_spec(temp as int) == extract_first_digit_spec(n as int)
    ensures temp as int == extract_first_digit_spec(n as int)
{
    assert(extract_first_digit_spec(temp as int) == temp as int);
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
    let mut i = 0;

    while i < numbers.len()
        invariant
            i <= numbers.len(),
            count <= i,
            count == special_filter_spec(numbers@.subrange(0, i as int)),
        decreases numbers.len() - i,
    {
        let n = numbers[i];
        
        if n > 10 {
            let first_digit = {
                let mut temp = n;
                while temp >= 10
                    invariant temp > 0, extract_first_digit_spec(temp as int) == extract_first_digit_spec(n as int)
                    decreases temp,
                {
                    temp = temp / 10;
                }
                proof {
                    lemma_extract_first_digit_correctness(temp, n);
                }
                temp
            };
            
            let last_digit = n % 10;
            
            if (first_digit % 2 != 0) && (last_digit % 2 != 0) {
                count = count + 1;
            }
        }
        
        proof {
            lemma_special_filter_spec_subrange(numbers@, (i + 1) as nat);
        }
        
        i = i + 1;
    }
    
    proof {
        assert(numbers@.subrange(0, numbers.len() as int) =~= numbers@);
    }
    
    count
}
// </vc-code>

} // verus!
fn main() {}