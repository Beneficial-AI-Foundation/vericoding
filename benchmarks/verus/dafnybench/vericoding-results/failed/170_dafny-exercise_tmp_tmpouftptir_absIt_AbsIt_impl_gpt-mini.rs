use vstd::prelude::*;

verus! {

// <vc-helpers>
// No helpers needed for this proof.
// </vc-helpers>

// <vc-spec>
fn abs_it(s: &mut Vec<i32>)
    ensures
        s.len() == old(s).len(),
        forall|i: int| 0 <= i < s.len() ==> 
            if old(s)[i] < 0 { s[i] == -old(s)[i] } else { s[i] == old(s)[i] }
// </vc-spec>
// <vc-code>
{
    let old_s: Seq<i32> = s@;
    let len_usize: usize = s.len();
    let mut i: usize = 0;
    while i < len_usize
        invariant 0 <= (i as int) && (i as int) <= (len_usize as int),
        s.len() == len_usize,
        forall|k: int| 0 <= k && k < (i as int) ==>
            #[trigger] if old_s[k] < 0 { (s@)[k] == -old_s[k] } else { (s@)[k] == old_s[k] },
        forall|k: int| (i as int) <= k && k < (len_usize as int) ==>
            #[trigger] (s@)[k] == old_s[k]
    {
        let v: i32 = s[i];
        if v < 0 {
            s[i] = -v;
        }
        i = i + 1;
    }
    proof {
        assert((s.len() as int) == old_s.len());
        assert(forall|k: int| 0 <= k && k < (len_usize as int) ==>
            if old_s[k] < 0 { (s@)[k] == -old_s[k] } else { (s@)[k] == old_s[k] });
    }
}
// </vc-code>

fn main() {}

}