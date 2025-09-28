use vstd::prelude::*;

verus! {

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn double_array_elements(s: &mut Vec<i32>)
    ensures forall|i: int| 0 <= i < old(s).len() ==> s[i] == 2 * old(s)[i]
// </vc-spec>
// <vc-code>
{
    let ghost old_s = s@;
    let n = s.len();
    let mut i: usize = 0;
    while i < n
        invariant
            s.len() == n
            && old_s.len() == n as int
            && 0 <= i as int && i as int <= n as int
            && (forall|j: int| 0 <= j && j < i as int ==> #[trigger] s@[j] == 2 * old_s[j])
            && (forall|j: int| i as int <= j && j < n as int ==> #[trigger] s@[j] == old_s[j])
    {
        let gi = i as int;
        assert(0 <= gi && gi < n as int);
        let v_i = s[i];
        proof {
            assert(s@[gi] == old_s[gi]);
            assert(v_i == s@[gi]);
            assert(v_i == old_s[gi]);
        }
        s[i] = 2 * v_i;
        proof {
            assert(s@[gi] == 2 * v_i);
            assert(s@[gi] == 2 * old_s[gi]);
        }
        i += 1;
    }
    proof {
        assert(i >= n);
        assert(i as int >= n as int);
        assert(i as int <= n as int);
        assert(i as int == n as int);
        assert(old_s == old(s)@);
    }
    assert(forall|j: int| 0 <= j && j < n as int ==> #[trigger] s@[j] == 2 * old_s[j]);
}
// </vc-code>

fn main() {
}

}