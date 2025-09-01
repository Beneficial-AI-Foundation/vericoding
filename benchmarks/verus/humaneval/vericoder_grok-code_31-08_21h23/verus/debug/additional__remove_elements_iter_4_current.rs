use vstd::prelude::*;

verus! {

spec fn in_array(a: Seq<i32>, x: i32) -> (ret: bool) {
    exists|i: int| 0 <= i < a.len() && a[i] == x
}

// <vc-helpers>
// No updates needed here as the duplicate definition is removed; the in_array function is already defined in the PREAMBLE
// </vc-helpers>

// <vc-spec>
#[verifier::loop_isolation(false)]
fn remove_elements(a: &Vec<i32>, b: &Vec<i32>) -> (c: Vec<i32>)
    // post-conditions-start
    ensures
        forall|k: int| #![auto] 0 <= k < c.len() ==> in_array(a@, c[k]) && !in_array(b@, c[k]),
        forall|i: int, j: int| 0 <= i < j < c.len() ==> c[i] != c[j],
    // post-conditions-end
// </vc-spec>
// <vc-code>
{
    let mut c: Vec<i32> = Vec::with_capacity(a.len());
    let a_seq: Seq<i32> = a@;
    let b_seq: Seq<i32> = b@;
    for index in 0..a.len()
        invariant
            forall|k: int| 0 <= k < c.len() ==> in_array(a_seq, c[k]) && !in_array(b_seq, c[k]),
            forall|i: int, j: int| 0 <= i < j < c.len() ==> c[i] != c[j],
    {
        let x = a@[index];
        let mut found_in_b: bool = false;
        for j in 0..b.len() {
            if b@[j] == x {
                found_in_b = true;
                break;
            }
        }
        proof {
            assert(found_in_b <==> in_array(b_seq, x));
        }
        if !found_in_b {
            let mut found_in_c: bool = false;
            for k in 0..c.len() {
                if c@[k] == x {
                    found_in_c = true;
                    break;
                }
            }
            proof {
                assert(found_in_c <==> in_array(c@, x));
            }
            if !found_in_c {
                c.push(x);
                proof {
                    assert(x == a_seq[index as int]);
                    assert(in_array(a_seq, x));
                    assert(!in_array(b_seq, x));
                    assert(forall|prev_k: int| 0 <= prev_k < old(c@).len() ==> old(c@)[prev_k] != x);
                }
            }
        }
    }
    c
}
// </vc-code>

fn main() {}
}