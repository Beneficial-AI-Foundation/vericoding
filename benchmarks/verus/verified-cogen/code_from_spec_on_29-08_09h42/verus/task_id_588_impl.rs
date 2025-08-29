#![verifier::loop_isolation(false)]
use vstd::math::*;
use vstd::prelude::*;

verus! {

spec fn max_rcur(seq: Seq<i32>) -> (result: int)
    decreases seq.len(),
{
    if seq.len() <= 1 {
        seq.first() as int
    } else {
        max(seq.last() as int, max_rcur(seq.drop_last()))
    }
}
// pure-end
// pure-end

spec fn min_rcur(seq: Seq<i32>) -> (result: int)
    decreases seq.len(),
{
    if seq.len() <= 1 {
        seq.first() as int
    } else {
        min(seq.last() as int, min_rcur(seq.drop_last()))
    }
}
// pure-end

// <vc-helpers>
spec fn max_iter_spec(seq: Seq<i32>, start: nat) -> int
    decreases seq.len() - start
{
    if start >= seq.len() {
        i32::MIN as int
    } else if start == seq.len() - 1 {
        seq[start as int] as int
    } else {
        max(seq[start as int] as int, max_iter_spec(seq, start + 1))
    }
}

spec fn min_iter_spec(seq: Seq<i32>, start: nat) -> int
    decreases seq.len() - start
{
    if start >= seq.len() {
        i32::MAX as int
    } else if start == seq.len() - 1 {
        seq[start as int] as int
    } else {
        min(seq[start as int] as int, min_iter_spec(seq, start + 1))
    }
}

proof fn max_iter_equiv_rcur(seq: Seq<i32>)
    requires seq.len() > 0
    ensures max_iter_spec(seq, 0) == max_rcur(seq)
    decreases seq.len()
{
    if seq.len() == 1 {
    } else {
        max_iter_equiv_rcur(seq.drop_last());
        assert(max_iter_spec(seq.drop_last(), 0) == max_rcur(seq.drop_last()));
        assert(seq.drop_last().len() > 0);
        max_iter_step(seq, 0);
    }
}

proof fn min_iter_equiv_rcur(seq: Seq<i32>)
    requires seq.len() > 0
    ensures min_iter_spec(seq, 0) == min_rcur(seq)
    decreases seq.len()
{
    if seq.len() == 1 {
    } else {
        min_iter_equiv_rcur(seq.drop_last());
        assert(min_iter_spec(seq.drop_last(), 0) == min_rcur(seq.drop_last()));
        assert(seq.drop_last().len() > 0);
        min_iter_step(seq, 0);
    }
}

proof fn max_iter_step(seq: Seq<i32>, start: nat)
    requires 
        start < seq.len(),
        seq.len() > 1,
        start == 0,
    ensures 
        max_iter_spec(seq, start) == max(seq.last() as int, max_iter_spec(seq.drop_last(), start))
    decreases seq.len() - start
{
    /* code modified by LLM (iteration 5): fixed missing else case for when start + 1 >= seq.len() */
    if start + 1 < seq.len() {
        max_iter_step_helper(seq, start);
        if seq.drop_last().len() > 1 {
            max_iter_step(seq.drop_last(), start);
        }
        
        assert(seq[start as int] == seq.drop_last()[start as int]);
        
        let left = max_iter_spec(seq, start);
        let right = max(seq.last() as int, max_iter_spec(seq.drop_last(), start));
        
        assert(left == max(seq[start as int] as int, max_iter_spec(seq, start + 1)));
        assert(right == max(seq.last() as int, max_iter_spec(seq.drop_last(), start)));
    } else {
        assert(start + 1 >= seq.len());
        assert(start == seq.len() - 1);
        assert(max_iter_spec(seq, start) == seq[start as int] as int);
        assert(seq[start as int] == seq.last());
        assert(max_iter_spec(seq.drop_last(), start) == i32::MIN as int);
        assert(max(seq.last() as int, max_iter_spec(seq.drop_last(), start)) == seq.last() as int);
    }
}

proof fn min_iter_step(seq: Seq<i32>, start: nat)
    requires 
        start < seq.len(),
        seq.len() > 1,
        start == 0,
    ensures 
        min_iter_spec(seq, start) == min(seq.last() as int, min_iter_spec(seq.drop_last(), start))
    decreases seq.len() - start
{
    /* code modified by LLM (iteration 5): fixed missing else case for when start + 1 >= seq.len() */
    if start + 1 < seq.len() {
        min_iter_step_helper(seq, start);
        if seq.drop_last().len() > 1 {
            min_iter_step(seq.drop_last(), start);
        }
        
        assert(seq[start as int] == seq.drop_last()[start as int]);
        
        let left = min_iter_spec(seq, start);
        let right = min(seq.last() as int, min_iter_spec(seq.drop_last(), start));
        
        assert(left == min(seq[start as int] as int, min_iter_spec(seq, start + 1)));
        assert(right == min(seq.last() as int, min_iter_spec(seq.drop_last(), start)));
    } else {
        assert(start + 1 >= seq.len());
        assert(start == seq.len() - 1);
        assert(min_iter_spec(seq, start) == seq[start as int] as int);
        assert(seq[start as int] == seq.last());
        assert(min_iter_spec(seq.drop_last(), start) == i32::MAX as int);
        assert(min(seq.last() as int, min_iter_spec(seq.drop_last(), start)) == seq.last() as int);
    }
}

proof fn max_iter_step_helper(seq: Seq<i32>, start: nat)
    requires 
        start < seq.len(),
        start + 1 < seq.len(),
    ensures 
        max_iter_spec(seq, start) == max(seq[start as int] as int, max_iter_spec(seq, start + 1))
{
}

proof fn min_iter_step_helper(seq: Seq<i32>, start: nat)
    requires 
        start < seq.len(),
        start + 1 < seq.len(),
    ensures 
        min_iter_spec(seq, start) == min(seq[start as int] as int, min_iter_spec(seq, start + 1))
{
}

proof fn subrange_max_correct(seq: Seq<i32>, len: nat)
    requires 
        len > 0,
        len <= seq.len(),
        seq.len() > 0
    ensures max_iter_spec(seq.subrange(0, len as int), 0) == max_iter_spec(seq, 0) || len < seq.len()
    decreases len
{
    if len == seq.len() {
        assert(seq.subrange(0, len as int) == seq);
    }
}

proof fn subrange_min_correct(seq: Seq<i32>, len: nat)
    requires 
        len > 0,
        len <= seq.len(),
        seq.len() > 0
    ensures min_iter_spec(seq.subrange(0, len as int), 0) == min_iter_spec(seq, 0) || len < seq.len()
    decreases len
{
    if len == seq.len() {
        assert(seq.subrange(0, len as int) == seq);
    }
}

proof fn max_property(seq: Seq<i32>, max_val: i32, max_idx: int)
    requires
        seq.len() > 0,
        0 <= max_idx < seq.len(),
        max_val == seq[max_idx],
        forall|j: int| 0 <= j < seq.len() ==> max_val >= seq[j],
    ensures max_val as int == max_rcur(seq)
    decreases seq.len()
{
    if seq.len() == 1 {
        assert(max_val == seq[0]);
        assert(max_rcur(seq) == seq.first() as int);
        assert(seq.first() == seq[0]);
    } else {
        if max_idx == seq.len() - 1 {
            let rest = seq.drop_last();
            assert(forall|j: int| 0 <= j < rest.len() ==> max_val >= rest[j]);
            if rest.len() > 0 {
                let max_rest = choose |k: int| 0 <= k < rest.len() && (forall|j: int| 0 <= j < rest.len() ==> rest[k] >= rest[j]);
                max_property(rest, rest[max_rest], max_rest);
                assert(max_rcur(rest) == rest[max_rest] as int);
                assert(max_rcur(seq) == max(seq.last() as int, max_rcur(rest)));
                assert(max_val as int >= max_rcur(rest));
                assert(max_val as int == seq.last() as int);
                assert(max_rcur(seq) == max_val as int);
            }
        } else {
            let rest = seq.drop_last();
            assert(0 <= max_idx < rest.len());
            assert(max_val == rest[max_idx]);
            assert(forall|j: int| 0 <= j < rest.len() ==> max_val >= rest[j]);
            max_property(rest, max_val, max_idx);
            assert(max_rcur(rest) == max_val as int);
            assert(max_rcur(seq) == max(seq.last() as int, max_rcur(rest)));
            assert(max_val >= seq.last());
            assert(max_rcur(seq) == max_val as int);
        }
    }
}

proof fn min_property(seq: Seq<i32>, min_val: i32, min_idx: int)
    requires
        seq.len() > 0,
        0 <= min_idx < seq.len(),
        min_val == seq[min_idx],
        forall|j: int| 0 <= j < seq.len() ==> min_val <= seq[j],
    ensures min_val as int == min_rcur(seq)
    decreases seq.len()
{
    if seq.len() == 1 {
        assert(min_val == seq[0]);
        assert(min_rcur(seq) == seq.first() as int);
        assert(seq.first() == seq[0]);
    } else {
        if min_idx == seq.len() - 1 {
            let rest = seq.drop_last();
            assert(forall|j: int| 0 <= j < rest.len() ==> min_val <= rest[j]);
            if rest.len() > 0 {
                let min_rest = choose |k: int| 0 <= k < rest.len() && (forall|j: int| 0 <= j < rest.len() ==> rest[k] <= rest[j]);
                min_property(rest, rest[min_rest], min_rest);
                assert(min_rcur(rest) == rest[min_rest] as int);
                assert(min_rcur(seq) == min(seq.last() as int, min_rcur(rest)));
                assert(min_val as int <= min_rcur(rest));
                assert(min_val as int == seq.last() as int);
                assert(min_rcur(seq) == min_val as int);
            }
        } else {
            let rest = seq.drop_last();
            assert(0 <= min_idx < rest.len());
            assert(min_val == rest[min_idx]);
            assert(forall|j: int| 0 <= j < rest.len() ==> min_val <= rest[j]);
            min_property(rest, min_val, min_idx);
            assert(min_rcur(rest) == min_val as int);
            assert(min_rcur(seq) == min(seq.last() as int, min_rcur(rest)));
            assert(min_val <= seq.last());
            assert(min_rcur(seq) == min_val as int);
        }
    }
}
// </vc-helpers>

// <vc-spec>
fn difference_max_min(arr: &Vec<i32>) -> (diff: i32)
    // pre-conditions-start
    requires
        arr.len() > 0,
        forall|i: int| 0 <= i < arr.len() ==> i32::MIN / 2 < #[trigger] arr[i] < i32::MAX / 2,
    // pre-conditions-end
    // post-conditions-start
    ensures
        diff == max_rcur(arr@) - min_rcur(arr@),
    // post-conditions-end
// </vc-spec>

// <vc-code>
{
    let mut max_val = arr[0];
    let mut min_val = arr[0];
    
    let mut i = 1;
    while i < arr.len()
        invariant
            1 <= i <= arr.len(),
            forall|j: int| 0 <= j < i ==> max_val >= arr[j],
            forall|j: int| 0 <= j < i ==> min_val <= arr[j],
            exists|k: int| 0 <= k < i && max_val == arr[k],
            exists|k: int| 0 <= k < i && min_val == arr[k],
        decreases arr.len() - i
    {
        if arr[i] > max_val {
            max_val = arr[i];
        }
        if arr[i] < min_val {
            min_val = arr[i];
        }
        i += 1;
    }
    
    /* code modified by LLM (iteration 5): use new helper proofs to establish connection to recursive specs */
    proof {
        assert(i == arr.len());
        assert(forall|j: int| 0 <= j < arr.len() ==> max_val >= arr[j]);
        assert(forall|j: int| 0 <= j < arr.len() ==> min_val <= arr[j]);
        
        let max_idx = choose |k: int| 0 <= k < arr.len() && max_val == arr[k];
        let min_idx = choose |k: int| 0 <= k < arr.len() && min_val == arr[k];
        
        max_property(arr@, max_val, max_idx);
        min_property(arr@, min_val, min_idx);
        
        assert(max_val as int - min_val as int >= i32::MIN / 2 - i32::MAX / 2);
        assert(max_val as int - min_val as int <= i32::MAX / 2 - i32::MIN / 2);
        assert(max_val - min_val == max_rcur(arr@) - min_rcur(arr@));
    }
    
    max_val - min_val
}
// </vc-code>

} // verus!

fn main() {}