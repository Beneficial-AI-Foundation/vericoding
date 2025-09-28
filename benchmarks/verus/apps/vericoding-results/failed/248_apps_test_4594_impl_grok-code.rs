// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_input(diameters: Seq<int>) -> bool {
    diameters.len() > 0 && forall|i: int| 0 <= i < diameters.len() ==> diameters[i] > 0
}

spec fn num_distinct(s: Seq<int>) -> int
    decreases s.len()
{
    if s.len() == 0 {
        0
    } else if s.subrange(1, s.len() as int).contains(s[0]) {
        num_distinct(s.subrange(1, s.len() as int))
    } else {
        1 + num_distinct(s.subrange(1, s.len() as int))
    }
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): fixed type mismatches by using correct sequence subrange syntax and mapping to Seq<int> for num_distinct */
fn contains_slice(list: &[i8], start: usize, val: i8) -> (res: bool)
    requires
        start <= list.len(),
    decreases
        list.len() - start,
{
    if start >= list.len() {
        false
    } else if list[start] == val {
        true
    } else {
        contains_slice(list, start + 1, val)
    }
}

/* helper modified by LLM (iteration 5): fixed type mismatches by using correct sequence subrange syntax */
fn count_distinct_slice(data: &[i8], start: usize) -> usize
    requires
        start <= data.len(),
    decreases
        data.len() - start,
{
    if start >= data.len() {
        0
    } else if contains_slice(data, start + 1, data[start]) {
        count_distinct_slice(data, start + 1)
    } else {
        1 + count_distinct_slice(data, start + 1)
    }
}

proof fn contains_slice_matches(data: &[i8], from: usize, val: i8)
    requires
        from <= data.len(),
    ensures
        contains_slice(data, from, val) == data@.subrange(from as int, data.len() as int).contains(val),
    decreases
        data.len() - from,
{
    if from >= data.len() {
        assert(data@.subrange(from as int, data.len() as int).len() == 0);
    } else {
        let sub_seq = data@.subrange(from as int + 1, data.len() as int);
        assert(data@.subrange(from as int, data.len() as int) == seq![data@[from as int]] + sub_seq);
        assert((seq![data@[from as int]] + sub_seq).contains(val) == (data@[from as int] == val || sub_seq.contains(val)));
    }
}

proof fn num_distinct_slice_matches(data: &[i8], start: usize)
    requires
        start <= data.len(),
    ensures
        count_distinct_slice(data, start) as int == num_distinct(data@.subrange(start as int, data.len() as int).map(|i: int, x: i8| x as int)),
    decreases
        data.len() - start,
{
    if start >= data.len() {
        assert(num_distinct(seq![]) == 0);
    } else {
        let sub_mapped = data@.subrange(start as int + 1, data.len() as int).map(|i: int, x: i8| x as int);
        let full_mapped = data@.subrange(start as int, data.len() as int).map(|i: int, x: i8| x as int);
        assert(full_mapped.subrange(1, full_mapped.len() as int) == sub_mapped);
        assert(full_mapped[0] == data@[start as int] as int);
        if contains_slice(data, start + 1, data[start]) {
            contains_slice_matches(data, start + 1, data[start]);
            num_distinct_slice_matches(data, start + 1);
        } else {
            contains_slice_matches(data, start + 1, data[start]);
            num_distinct_slice_matches(data, start + 1);
        }
    }
}
// </vc-helpers>

// <vc-spec>
fn solve(diameters: Vec<i8>) -> (result: i8)
    requires 
        valid_input(diameters@.map(|i, x| x as int)),
    ensures 
        result as int == num_distinct(diameters@.map(|i, x| x as int)),
        result as int >= 1,
        result as int <= diameters@.len(),
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): fixed proof assertions to use correct syntax */
{
    let count = count_distinct_slice(&diameters, 0);
    proof {
        num_distinct_slice_matches(&diameters, 0);
        assert(count as int == num_distinct(diameters@.map(|i, x| x as int)));
    }
    count as i8
}
// </vc-code>


}

fn main() {}