use vstd::prelude::*;

verus! {

// <vc-helpers>
fn contains_duplicate(s: Seq<i32>) -> bool {
    let mut i: u64 = 0;
    while (i as int) < s.len()
        invariant
            0 <= i as int <= s.len(),
            s.len() == old(s).len(),
    {
        let mut j: u64 = i + 1;
        while (j as int) < s.len()
            invariant
                (i as int) < (j as int) <= s.len(),
                (i as int) < s.len(),
                s.len() == old(s).len(),
        {
            if s.index(i as int) == s.index(j as int) {
                return true;
            }
            j = j + 1;
        }
        i = i + 1;
    }
    false
}
// </vc-helpers>

// <vc-spec>
fn remove_duplicates(a: &[i32]) -> (result: Vec<i32>)
    ensures
        forall|x: i32| result@.contains(x) <==> exists|i: int| 0 <= i < a.len() && a[i] == x,
        forall|i: int, j: int| 0 <= i < j < result.len() ==> result@[i] != result@[j]
// </vc-spec>
// <vc-code>
{
    let mut result: Vec<i32> = Vec::new();
    let mut i: u64 = 0;

    while (i as int) < a.len()
        invariant
            0 <= i as int <= a.len(),
            forall|x: i32| result@.contains(x) <==> exists|k: int| 0 <= k < i as int && a[k as int] == x,
            forall|u: int, v: int| 0 <= u < v < result.len() ==> result@[u] != result@[v],
            result.len() <= i as int,
    {
        let current_val = a[i as usize];

        let mut found = false;
        let mut j: u64 = 0;
        while (j as int) < result.len()
            invariant
                0 <= j as int <= result.len(),
                found == exists|k: int| 0 <= k < j as int && result@[k as int] == current_val,
                result.len() == old(result.len()),
                forall|u: int, v: int| 0 <= u < v < result.len() ==> result@[u] != result@[v],
        {
            if result@[j as int] == current_val {
                found = true;
            }
            j = j + 1;
        }

        if !found {
            result.push(current_val);
            proof {
                assert forall|u: int, v: int| 0 <= u < v < (result.len() as int) implies result@[u] != result@[v] by {
                    if v == (result.len() - 1) as int {
                        assert(result@[u] != current_val);
                    }
                }
            }
        }
        i = i + 1;
    }
    result
}
// </vc-code>

fn main() {
}

}