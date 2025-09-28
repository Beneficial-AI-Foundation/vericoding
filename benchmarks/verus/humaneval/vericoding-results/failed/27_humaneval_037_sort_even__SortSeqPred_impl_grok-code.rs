// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
use vstd::seq_lib::*;

fn insertion_sort_seq(seq: Seq<i8>) -> (ret: Seq<i8>)
    ensures
        ret.len() == seq.len(),
        forall|i: int, j: int| 0 <= i < j < ret.len() ==> (ret[i] as int) <= (ret[j] as int),
        seq.to_multiset() == ret.to_multiset(),
{
    if seq.len() <= 1 {
        return seq;
    }
    let mut result = Seq::new(seq.len(), |i| seq[i]);
    let mut i = 1;
    while i < seq.len()
        invariant
            result.len() == seq.len(),
            0 < i <= seq.len(),
            forall|k: int, l: int| 0 <= k < l < i ==> (result[k] as int) <= (result[l] as int),
            seq.to_multiset() == result.to_multiset(),
        decreases seq.len() - i,
    {
        let key = result[i];
        let mut j = i;
        while j > 0 && (result[j-1] as int) > (key as int)
            invariant
                0 <= j <= i,
                result.len() == seq.len(),
                forall|m: int, n: int| 0 <= m < n < i+1 && n != j ==> (result[m] as int) <= (result[n] as int),
                seq.to_multiset() == result.to_multiset(),
            decreases j,
        {
            result = result.update(j, result[j-1]);
            j = j - 1;
        }
        result = result.update(j, key);
        i = i + 1;
    }
    result
}

fn sort_vec(v: Vec<i8>) -> (ret: Vec<i8>)
    ensures
        ret@.len() == v@.len(),
        forall|i: int, j: int| 0 <= i < j < v@.len() ==> (ret@[i] as int) <= (ret@[j] as int),
        v@.to_multiset() == ret@.to_multiset(),
{
    let sorted_seq = insertion_sort_seq(v@);
    let mut result = Vec::with_capacity(sorted_seq.len() as usize);
    let mut i: usize = 0;
    while i < sorted_seq.len()
        invariant
            i <= sorted_seq.len(),
            result@.len() == i,
            forall|j: int| 0 <= j < i ==> result@[j] == sorted_seq[j],
        decreases sorted_seq.len() - i,
    {
        result.push(sorted_seq[i]);
        i = i + 1;
    }
    result
}
// </vc-helpers>

// <vc-spec>
fn sort_seq_pred(s: Vec<i8>, p: Vec<bool>) -> (sorted: Vec<i8>)
    requires s.len() == p.len(),
    ensures 
        sorted.len() == s.len(),
        forall|i: int, j: int| 0 <= i < j < sorted.len() && p[i as int] && p[j as int] ==> sorted[i] as int <= sorted[j] as int,
        s@.to_multiset() == sorted@.to_multiset(),
        forall|i: int| 0 <= i < s.len() && !p[i as int] ==> sorted[i] == s[i],
// </vc-spec>
// <vc-code>
{
/* code modified by LLM (iteration 5): fixed compilation error by using int for loop indices to avoid type mismatches */
    let mut to_sort = Vec::new();
    let mut i: int = 0;
    while i < (s.len() as int)
        invariant
            i <= (s.len() as int),
            to_sort@.len() == (p@.subrange(0, i)).filter(|x| true).len(),
            to_sort@.to_multiset() == s@.subrange(0, i).zip(p@.subrange(0, i)).filter(|pair| pair.1).map(|pair| pair.0).to_multiset(),
        decreases (s.len() as int) - i,
    {
        if p@[(i as usize)] {
            to_sort.push(s@[(i as usize)]);
        }
        i = i + 1;
    }
    let sorted_to_sort = sort_vec(to_sort);
    let mut sorted = Vec::new();
    let mut idx: int = 0;
    let mut known_idx: int = 0;
    while known_idx < (s.len() as int)
        invariant
            sorted@.len() == known_idx,
            idx == sorted_to_sort@.len() + (p@.subrange(0, known_idx)).filter(|x| false).len() - (p@.subrange(0, known_idx)).filter(|x| true).len(),
            forall|k: int| 0 <= k < known_idx && !p@[k] ==> sorted@[k] == s@[k],
        decreases (s.len() as int) - known_idx,
    {
        let val = if p@[(known_idx as usize)] {
            let val = sorted_to_sort@[(idx as usize)];
            idx = idx + 1;
            val
        } else {
            s@[(known_idx as usize)]
        };
        sorted.push(val);
        known_idx = known_idx + 1;
    }
    sorted
}
// </vc-code>


}

fn main() {}