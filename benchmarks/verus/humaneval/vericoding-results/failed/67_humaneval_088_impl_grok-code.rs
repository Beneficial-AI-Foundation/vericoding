// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn valid_input(arr: Seq<int>) -> bool {
    forall|i: int| 0 <= i < arr.len() ==> arr[i] >= 0
}

spec fn is_ascending_sorted(s: Seq<int>) -> bool {
    forall|i: int, j: int| 0 <= i < j < s.len() ==> s[i] <= s[j]
}

spec fn is_descending_sorted(s: Seq<int>) -> bool {
    forall|i: int, j: int| 0 <= i < j < s.len() ==> s[i] >= s[j]
}

spec fn should_sort_ascending(arr: Seq<int>) -> bool {
    arr.len() > 1 && (arr[0] + arr[arr.len() - 1]) % 2 == 1
}

spec fn should_sort_descending(arr: Seq<int>) -> bool {
    arr.len() > 1 && (arr[0] + arr[arr.len() - 1]) % 2 == 0
}

spec fn correctly_sorted(arr: Seq<int>, result: Seq<int>) -> bool {
    (arr.len() <= 1 ==> result == arr) &&
    (should_sort_ascending(arr) ==> is_ascending_sorted(result)) &&
    (should_sort_descending(arr) ==> is_descending_sorted(result))
}

fn sort_ascending(arr: Seq<int>) -> (result: Seq<int>)
    ensures
        result.to_multiset() == arr.to_multiset(),
        is_ascending_sorted(result)
{
    assume(false);
    unreached()
}


fn sort_descending(arr: Seq<int>) -> (result: Seq<int>)
    ensures
        result.to_multiset() == arr.to_multiset(),
        is_descending_sorted(result)
{
    assume(false);
    unreached()
}

// </vc-preamble>

// <vc-helpers> 
/* helper modified by LLM (iteration 5): implemented sort_ascending_h with tracked to handle ghost Seq, fixed index types to nat, used @ for indexing and subrange for slicing */
fn sort_ascending_h(arr: Seq<int>) -> (result: Seq<int>)
    ensures
        result.to_multiset() == arr.to_multiset(),
        is_ascending_sorted(result)
{
    tracked {
        if arr.len() == 0 {
            Seq::<int>::empty()
        } else {
            let mut sorted = Seq::<int>::empty();
            sorted = sorted.push(arr@[0]);
            let mut i: nat = 1;
            while i < arr.len()
                invariant
                    i <= arr.len(),
                    sorted.len() == i as int,
                    is_ascending_sorted(sorted),
                    sorted.to_multiset() == arr@[..i as int].to_multiset(),
                decreases arr.len() - i
            {
                let curr = arr@[(i as int)];
                let mut pos: nat = 0;
                while pos < sorted.len() && sorted@[(pos as int)] <= curr
                    invariant
                        pos <= sorted.len(),
                        forall|k: int| 0 <= k < pos ==> sorted@[k] <= curr,
                    decreases sorted.len() - pos
                {
                    pos += 1;
                }
                sorted = sorted.subrange(0, pos) + Seq::<int>::empty().push(curr) + sorted.subrange(pos, sorted.len());
                i += 1;
            }
            sorted
        }
    }
}

/* helper modified by LLM (iteration 5): implemented sort_descending_h with tracked to handle ghost Seq, fixed index types to nat, used @ for indexing and subrange for slicing */
fn sort_descending_h(arr: Seq<int>) -> (result: Seq<int>)
    ensures
        result.to_multiset() == arr.to_multiset(),
        is_descending_sorted(result)
{
    tracked {
        if arr.len() == 0 {
            Seq::<int>::empty()
        } else {
            let mut sorted = Seq::<int>::empty();
            sorted = sorted.push(arr@[0]);
            let mut i: nat = 1;
            while i < arr.len()
                invariant
                    i <= arr.len(),
                    sorted.len() == i as int,
                    is_descending_sorted(sorted),
                    sorted.to_multiset() == arr@[..i as int].to_multiset(),
                decreases arr.len() - i
            {
                let curr = arr@[(i as int)];
                let mut pos: nat = 0;
                while pos < sorted.len() && sorted@[(pos as int)] >= curr
                    invariant
                        pos <= sorted.len(),
                        forall|k: int| 0 <= k < pos ==> sorted@[k] >= curr,
                    decreases sorted.len() - pos
                {
                    pos += 1;
                }
                sorted = sorted.subrange(0, pos) + Seq::<int>::empty().push(curr) + sorted.subrange(pos, sorted.len());
                i += 1;
            }
            sorted
        }
    }
}
// </vc-helpers>


// <vc-spec>
fn sort_array(arr: Vec<i8>) -> (result: Vec<i8>)
    requires valid_input(arr@.map(|i: int, x: i8| x as int))
    ensures 
        result@.map(|i: int, x: i8| x as int).to_multiset() == arr@.map(|i: int, x: i8| x as int).to_multiset(),
        correctly_sorted(arr@.map(|i: int, x: i8| x as int), result@.map(|i: int, x: i8| x as int))
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): fixed type matching with as nat for comparisons, @ for ghost indexing */
{
    let tracked seq_arr: Seq<int>;
    proof {
        seq_arr = arr@.map(|i: int, x: i8| x as int);
    }
    let result_seq: Seq<int>;
    proof {
        if seq_arr.len() <= 1 {
            result_seq = seq_arr;
        } else if should_sort_ascending(seq_arr) {
            result_seq = sort_ascending_h(seq_arr);
        } else if should_sort_descending(seq_arr) {
            result_seq = sort_descending_h(seq_arr);
        } else {
            result_seq = seq_arr;
        }
    }
    let mut result = Vec::<i8>::new();
    let mut i: usize = 0;
    while (i as int) < result_seq.len()
        invariant
            i as int <= result_seq.len(),
            result@.len() == i,
            forall|j: int| 0 <= j < i as int ==> (result@[j] as int) == result_seq@[j],
        decreases result_seq.len() - (i as int)
    {
        result.push(result_seq@[(i as int)] as i8);
        i += 1;
    }
    result
}
// </vc-code>


}

fn main() {}