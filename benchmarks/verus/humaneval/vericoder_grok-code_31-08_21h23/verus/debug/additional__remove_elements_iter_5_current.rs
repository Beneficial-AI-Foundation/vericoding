use vstd::prelude::*;

verus! {

spec fn in_array(a: Seq<i32>, x: i32) -> (ret: bool) {
    exists|i: int| 0 <= i < a.len() && a[i] == x
}

// <vc-helpers>
spec fn in_array(a: Seq<i32>, x: i32) -> (ret: bool) {
    exists|i: int| #![trigger(a[i])] 0 <= i < a.len() && a[i] == x
}
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
            forall|k: int| #![auto] 0 <= k < c.len() ==> in_array(a_seq, c@[k]) && !in_array(b_seq, c@[k]),
            forall|i: int, j: int| #![auto] 0 <= i < j < c.len() ==> c@[i] != c@[j],
    {
        let x = a_seq[index as int];
        let mut found_in_b: bool = false;
        for j in 0..b.len()
            invariant
                found_in_b <==> exists|jj: int| #![trigger(b_seq[jj])] 0 <= jj < b_seq.len() && b_seq[jj] == x && jj < j as int,
        {
            if b_seq[j as int] == x {
                found_in_b = true;
                break;
            }
        }
        proof {
            assert(found_in_b <==> in_array(b_seq, x));
        }
        if !found_in_b {
            let mut found_in_c: bool = false;
            for k in 0..c.len()
                invariant
                    found_in_c <==> exists|kk: int| #![trigger((c@)[kk])] 0 <= kk < c.len() && c@[kk] == x && kk < k as int,
            {
                if c@[k as int] == x {
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
                }
            }
        }
    }
    c
}
// </vc-code>

fn main() {}
}