use vstd::prelude::*;

verus! {

spec fn has_count(v: int, a: Seq<int>, n: nat) -> int
    decreases n
{
    if n == 0 {
        0
    } else {
        if a[n-1] == v {
            has_count(v, a, (n-1) as nat) + 1
        } else {
            has_count(v, a, (n-1) as nat)
        }
    }
}

// <vc-helpers>
// (no helpers needed)
// </vc-helpers>

// <vc-spec>
fn count(v: i32, a: &[i32], n: usize) -> (r: i32)
    requires n <= a.len()
    ensures n <= a.len() ==> has_count(v as int, a@.map_values(|x: i32| x as int), n as nat) == r as int
// </vc-spec>
// <vc-code>
{
    let v_int: int = v as int;
    let seq: Seq<int> = a@.map_values(|x: i32| x as int);
    let mut i: usize = 0;
    let mut c: i32 = 0;
    while i < n
        invariant i <= n;
        invariant has_count(v_int, seq, i as nat) == c as int;
        decreases n - i;
    {
        if a[i] == v {
            proof {
                // relate sequence element to slice element
                assert(seq@[i as nat] == a[i] as int);
                // by equality a[i] == v we get seq@[i] == v_int
                assert(seq@[i as nat] == v_int);
                // unfold has_count for i+1
                assert(has_count(v_int, seq, (i+1) as nat) ==
                       if seq@[i as nat] == v_int {
                           has_count(v_int, seq, i as nat) + 1
                       } else {
                           has_count(v_int, seq, i as nat)
                       });
                // use invariant has_count(..., i) == c
                assert(has_count(v_int, seq, i as nat) == c as int);
                // conclude the new has_count equals c+1
                assert(has_count(v_int, seq, (i+1) as nat) == (c + 1) as int);
            }
            c = c + 1;
        } else {
            proof {
                // relate sequence element to slice element
                assert(seq@[i as nat] == a[i] as int);
                // a[i] != v implies seq@[i] != v_int
                assert(seq@[i as nat] != v_int);
                // unfold has_count for i+1
                assert(has_count(v_int, seq, (i+1) as nat) ==
                       if seq@[i as nat] == v_int {
                           has_count(v_int, seq, i as nat) + 1
                       } else {
                           has_count(v_int, seq, i as nat)
                       });
                // use invariant has_count(..., i) == c
                assert(has_count(v_int, seq, i as nat) == c as int);
                // conclude the new has_count equals c
                assert(has_count(v_int, seq, (i+1) as nat) == c as int);
            }
        }
        i += 1;
    }
    c
}
// </vc-code>

fn main() {
}

}