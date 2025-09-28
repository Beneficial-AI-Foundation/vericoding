// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn is_positive(x: int) -> bool {
    x > 0
}

spec fn all_positive(s: Seq<int>) -> bool {
    forall|i: int| 0 <= i < s.len() ==> is_positive(#[trigger] s[i])
}

spec fn all_elements_from_original(result: Seq<int>, original: Seq<int>) -> bool {
    forall|x: int| #[trigger] result.contains(x) ==> original.contains(x)
}

spec fn contains_all_positives(result: Seq<int>, original: Seq<int>) -> bool {
    forall|i: int| 0 <= i < original.len() && is_positive(original[i]) ==> result.contains(#[trigger] original[i])
}

spec fn preserves_order(result: Seq<int>, original: Seq<int>) -> bool {
    forall|i: int, j: int| 0 <= i < j < result.len() ==> 
        (exists|k1: int, k2: int| 0 <= k1 < k2 < original.len() && original[k1] == #[trigger] result[i] && original[k2] == #[trigger] result[j] &&
        forall|k: int| k1 < k < k2 ==> !is_positive(#[trigger] original[k]))
}

spec fn count_positives(s: Seq<int>) -> int {
    s.len() as int
}
// </vc-preamble>

// <vc-helpers>
fn index_of_first_positive(s: Seq<int>, start: int) -> (index: int)
    requires
        0 <= start <= s.len(),
        exists|i: int| start <= i < s.len() && is_positive(#[trigger] s[i]),
    ensures
        start <= index < s.len(),
        is_positive(s[index]),
        forall|i: int| start <= i < index ==> !is_positive(s[i]),
{
    let mut i = start;
    while i < s.len()
        invariant
            start <= i <= s.len(),
            exists|j: int| i <= j < s.len() && is_positive(s[j]),
            forall|j: int| start <= j < i ==> !is_positive(s[j]),
        decreases s.len() - i,
    {
        if is_positive(s[i]) {
            return i;
        }
        i += 1;
    }
    proof {
        assert(false);
    }
    i
}
// </vc-helpers>

// <vc-spec>
fn get_positive(l: Vec<i8>) -> (result: Vec<i8>)
    ensures 
        all_positive(result@.map(|i: int, x: i8| x as int)),
        all_elements_from_original(result@.map(|i: int, x: i8| x as int), l@.map(|i: int, x: i8| x as int)),
        contains_all_positives(result@.map(|i: int, x: i8| x as int), l@.map(|i: int, x: i8| x as int)),
        result.len() == count_positives(l@.map(|i: int, x: i8| x as int)),
        preserves_order(result@.map(|i: int, x: i8| x as int), l@.map(|i: int, x: i8| x as int)),
// </vc-spec>
// <vc-code>
{
    let mut result = Vec::new();
    let mut i = 0;
    let n = l.len();
    
    while i < n
        invariant
            0 <= i <= n,
            all_positive(result@.map(|j: int, x: i8| x as int)),
            all_elements_from_original(result@.map(|j: int, x: i8| x as int), l@.map(|j: int, x: i8| x as int)),
            forall|k: int| 0 <= k < i && is_positive(l@[k] as int) ==> result@.map(|j: int, x: i8| x as int).contains(l@[k] as int),
            result.len() == (forall|k: int| 0 <= k < i && is_positive(l@[k] as int)).count() as int,
            preserves_order(result@.map(|j: int, x: i8| x as int), l@.map(|j: int, x: i8| x as int)),
        decreases n - i,
    {
        if l[i] > 0 {
            result.push(l[i]);
        }
        i += 1;
    }
    
    result
}
// </vc-code>


}

fn main() {}