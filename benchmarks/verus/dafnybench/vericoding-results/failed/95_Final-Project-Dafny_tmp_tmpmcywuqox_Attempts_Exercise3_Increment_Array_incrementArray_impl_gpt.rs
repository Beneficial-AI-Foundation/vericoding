use vstd::prelude::*;

verus! {

// <vc-helpers>
// (no changes)
// </vc-helpers>

// <vc-spec>
fn increment_array(a: &mut Vec<i32>)
  requires old(a).len() > 0,
  ensures 
      a.len() == old(a).len(),
      forall|i: int| 0 <= i < a.len() ==> a[i] == old(a)[i] + 1,
// </vc-spec>
// <vc-code>
{
    let n = a.len();
    let ghost n_int: int = n as int;
    let ghost old_seq = a@;

    let mut i: usize = 0;
    while i < n
        invariant
            a.len() == n,
            0 <= i as int && i as int <= n_int,
            forall|j: int| 0 <= j < i as int ==> #[trigger] a@[j] == old_seq[j] + 1,
            forall|j: int| i as int <= j < n_int ==> #[trigger] a@[j] == old_seq[j]
        decreases n_int - i as int
    {
        let v_i = a[i];
        assert(0 <= i as int);
        assert(i as int < n_int);
        assert(v_i == a@[i as int]);
        assert(a@[i as int] == old_seq[i as int]);

        a[i] = v_i + 1;
        i += 1;
    }

    assert(a.len() == n);
    assert(i as int == n_int);
    assert(forall|j: int| 0 <= j < n_int ==> #[trigger] a@[j] == old_seq[j] + 1);
}
// </vc-code>

fn main() {}

}