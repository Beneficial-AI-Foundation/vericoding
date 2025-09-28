use vstd::prelude::*;

verus! {

// <vc-helpers>
// No helpers needed
// </vc-helpers>

// <vc-spec>
fn remove_duplicates(a: &[i32]) -> (result: Vec<i32>)
    ensures
        forall|x: i32| result@.contains(x) <==> exists|i: int| 0 <= i < a.len() && a[i] == x,
        forall|i: int, j: int| 0 <= i < j < result.len() ==> result@[i] != result@[j]
// </vc-spec>
// <vc-code>
{
    let mut res: Vec<i32> = Vec::new();
    let mut i: int = 0;
    let n: int = a.len() as int;
    while i < n
        invariant 0 <= i && i <= n;
        invariant forall|v: i32| res@.contains(v) <==> exists|t: int| 0 <= t && t < i && a[t] == v;
        invariant forall|p: int, q: int| 0 <= p && p < q && q < res.len() as int ==> res@[p] != res@[q];
        decreases n - i
    {
        let x: i32 = a[i as usize];
        let mut j: int = 0;
        let mut found: bool = false;
        while j < res.len() as int
            invariant 0 <= j && j <= res.len() as int;
            invariant found == (exists|k: int| 0 <= k && k < j && res@[k] == x);
            decreases (res.len() as int) - j
        {
            if res[j as usize] == x {
                found = true;
            }
            j += 1;
        }

        if !found {
            let old_len: int = res.len() as int;
            proof {
                assert(old_len == res.len() as int);
                assert(!found);
                assert(found == (exists|k: int| 0 <= k && k < old_len && res@[k] == x));
                assert(! (exists|k: int| 0 <= k && k < old_len && res@[k] == x));
                assert(forall|v: i32| res@.contains(v) <==> exists|t: int| 0 <= t && t < i && a[t] == v);
                assert(forall|v: i32| (exists|t: int| 0 <= t && t < i && a[t] == v) <==> (exists|k: int| 0 <= k && k < old_len && res@[k] == v));
            }

            res.push(x);

            proof {
                assert(forall|v: i32|
                    res@.contains(v) <==>
                        (exists|t: int| 0 <= t && t < i+1 && a[t] == v)
                );
                assert(forall|p:int, q:int| 0 <= p && p < q && q < res.len() as int ==> res@[p] != res@[q]);
            }
        }

        i += 1;
    }

    res
}
// </vc-code>

fn main() {
}

}