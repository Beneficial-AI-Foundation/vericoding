// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn valid_input(l: Seq<int>) -> bool {
    l.len() > 0
}

spec fn is_max_element(l: Seq<int>, max_val: int) -> bool {
    l.contains(max_val) && forall|i: int| 0 <= i < l.len() ==> l[i] <= max_val
}

spec fn max_element_func(l: Seq<int>) -> int
    decreases l.len()
{
    if l.len() == 1 {
        l[0]
    } else if l.len() > 1 {
        let rest_max = max_element_func(l.subrange(1, l.len() as int));
        if l[0] > rest_max { l[0] } else { rest_max }
    } else {
        0int
    }
}

// </vc-preamble>

// <vc-helpers>
spec fn prefix_max(s: Seq<int>, i: int, max_val: int) -> bool {
    i >= 0 && i <= s.len() &&
    (i > 0 ==> 
        (exists|j: int| 0 <= j < i && s[j] == max_val) &&
        (forall|j: int| 0 <= j < i ==> s[j] <= max_val)
    )
}
// </vc-helpers>

// <vc-spec>
fn find_max_element(l: Vec<i8>) -> (max_val: i8)
    requires valid_input(l@.map(|i, x| x as int))
    ensures is_max_element(l@.map(|i, x| x as int), max_val as int)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 4): added initial proof block and restructured loop body with case analysis in proof */
{
    let len = l.len();
    let mut max_val = l[0];
    let mut i = 1;

    // Prove initial invariant
    proof {
        let s = l@.map(|i,x|x as int);
        assert(s.len() == l.len());
        assert(l.len() >= 1);
        assert(1 <= s.len());
        // Show the prefix condition for the initial state: prefix [0,1) and max_val = l[0] as int
        assert(s[0] == l[0] as int);
        // For the prefix [0,1):
        //   exists j in [0,1): j=0 -> s[0] == l[0] as int -> true.
        //   for all j in [0,1): j=0 -> s[0] <= l[0] as int -> true.
        assert(prefix_max(s, 1, l[0] as int));
        // Since max_val = l[0], we have l[0] as int == max_val as int.
        assert(l[0] as int == max_val as int);
        assert(prefix_max(s, 1, max_val as int));
    }

    while i < len
        invariant 
            1 <= i <= len,
            prefix_max(l@.map(|i, x| x as int), i as int, max_val as int),
        decreases len - i
    {
        let old_max_val = max_val;
        if l[i] > max_val {
            max_val = l[i];
        }
        proof {
            let s = l@.map(|i,x|x as int);
            // The invariant at the start of the loop body: 
            //   prefix_max(s, i, old_max_val as int)
            if max_val == old_max_val {
                // Not updated: then we have s[i] <= old_max_val as int.
                // We need to show: prefix_max(s, i+1, max_val as int) [which is old_max_val as int]
                // By the invariant at the start:
                //   exists j0 in [0, i) such that s[j0] == old_max_val as int -> and j0 is in [0, i+1).
                //   and for all j in [0, i): s[j] <= old_max_val as int.
                // Also, s[i] <= old_max_val as int (because we didn't update).
                // Therefore, for all j in [0, i+1): 
                //   if j < i: s[j] <= old_max_val as int = max_val as int.
                //   if j == i: s[j] <= old_max_val as int = max_val as int.
                // And we have j0 in [0, i+1) such that s[j0] == max_val as int.
                assert(prefix_max(s, i+1, max_val as int));
            } else {
                // Updated: then max_val = l[i] and max_val as int = s[i], and we have s[i] > old_max_val as int.
                // We need to show: prefix_max(s, i+1, max_val as int)
                //   - exists j in [0, i+1) such that s[j] == max_val as int: j=i -> s[i] = max_val as int -> true.
                //   - for all j in [0, i+1):
                //        if j < i: by the invariant at the start, s[j] <= old_max_val as int < s[i] = max_val as int -> so s[j] < max_val as int -> implies s[j] <= max_val as int.
                //        if j == i: s[j] = max_val as int -> so <= max_val as int.
                assert(prefix_max(s, i+1, max_val as int));
            }
        }
        i = i + 1;
    }

    max_val
}
// </vc-code>


}

fn main() {}