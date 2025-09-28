// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_input(n: int, f: Seq<int>) -> bool {
    n >= 2 && n <= 5000 &&
    f.len() == n &&
    forall|i: int| 0 <= i < f.len() ==> 1 <= f[i] <= n && f[i] != i + 1
}

spec fn zero_indexed_array(n: int, f: Seq<int>) -> Seq<int>
    recommends valid_input(n, f)
{
    Seq::new(n as nat, |j: int| f[j] - 1)
}

spec fn has_love_triangle_with(n: int, a: Seq<int>) -> bool
    recommends 
        a.len() == n &&
        forall|k: int| 0 <= k < n ==> #[trigger] a[k] >= 0 && #[trigger] a[k] < n
{
    exists|i: int| 0 <= i < n && 
        0 <= a[i] < n && 0 <= a[a[i]] < n && a[a[a[i]]] == i
}

spec fn has_love_triangle(n: int, f: Seq<int>) -> bool
    recommends valid_input(n, f)
{
    let a = zero_indexed_array(n, f);
    has_love_triangle_with(n, a)
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): provide witness for existence of triangle */
fn found_impl_implies_has(n: int, a: Seq<int>, idx: int)
    requires
        0 <= idx < n,
        a.len() == n,
        0 <= a[idx] < n,
        0 <= a[a[idx]] < n,
        a[a[a[idx]]] == idx,
    ensures
        has_love_triangle_with(n, a),
{
    assert(exists|i: int| 0 <= i < n && 0 <= a[i] < n && 0 <= a[a[i]] < n && a[a[a[i]]] == i);
}

/* helper modified by LLM (iteration 5): derive absence of triangle from universal negation */
fn none_impl_not_has(n: int, a: Seq<int>)
    requires
        a.len() == n,
        forall|i: int| 0 <= i < n ==> !(0 <= a[i] < n && 0 <= a[a[i]] < n && a[a[a[i]]] == i),
    ensures
        !has_love_triangle_with(n, a),
{
    assert(!(exists|i: int| 0 <= i < n && 0 <= a[i] < n && 0 <= a[a[i]] < n && a[a[a[i]]] == i));
}

// </vc-helpers>

// <vc-spec>
fn solve(n: i8, f: Vec<i8>) -> (result: String)
    requires 
        valid_input(n as int, f@.map(|i: int, x: i8| x as int)),
    ensures 
        result@.len() == 2 || result@.len() == 3,
        (result@.len() == 3) <==> has_love_triangle(n as int, f@.map(|i: int, x: i8| x as int)),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): build zero-indexed array and search for triangle; maintain ghost correspondence */
    let n_usize: usize = n as usize;
    let mut a: Vec<i8> = Vec::new();
    let mut i: usize = 0;
    while i < n_usize
        invariant
            0 <= i as int,
            i <= n_usize,
            forall|j: int| 0 <= j < i as int ==> a@[j] as int == (f@[j] as int) - 1,
        decreases n_usize - i,
    {
        let v_ref = f.get(i).unwrap();
        a.push(*v_ref - 1);
        i += 1;
    }

    let mut found: bool = false;
    let mut fi_usize: usize = 0;
    let mut idx: usize = 0;
    while idx < n_usize
        invariant
            0 <= idx as int,
            idx <= n_usize,
        decreases n_usize - idx,
    {
        let ai = a[idx] as i32;
        if ai >= 0 && (ai as usize) < n_usize {
            let ai_us = ai as usize;
            let aai = a[ai_us] as i32;
            if aai >= 0 && (aai as usize) < n_usize {
                let aai_us = aai as usize;
                let aaai = a[aai_us] as i32;
                if aaai == idx as i32 {
                    found = true;
                    fi_usize = idx;
                    break;
                }
            }
        }
        idx += 1;
    }

    let result = if found { String::from_str("YES") } else { String::from_str("NO") };

    proof {
        let fseq = f@.map(|i: int, x: i8| x as int);
        let a_seq = zero_indexed_array(n as int, fseq);

        assert(forall|j: int| 0 <= j < n as int ==> a@[j] as int == a_seq[j]);

        if found {
            let fi: int = fi_usize as int;
            assert(0 <= fi && fi < n as int);

            assert(0 <= a_seq[fi] && a_seq[fi] < n as int);
            let ai_int: int = a_seq[fi];
            assert(0 <= ai_int && ai_int < n as int);

            assert(0 <= a_seq[ai_int] && a_seq[ai_int] < n as int);
            let aai_int: int = a_seq[ai_int];
            assert(0 <= aai_int && aai_int < n as int);

            assert(a_seq[aai_int] == fi);
            assert(a_seq[a_seq[a_seq[fi]]] == fi);

            found_impl_implies_has(n as int, a_seq, fi);
        } else {
            assert(forall|i: int| 0 <= i < n as int ==> !(0 <= a_seq[i] < n as int && 0 <= a_seq[a_seq[i]] < n as int && a_seq[a_seq[a_seq[i]]] == i));
            none_impl_not_has(n as int, a_seq);
        }
    }

    result
}

// </vc-code>


}

fn main() {}