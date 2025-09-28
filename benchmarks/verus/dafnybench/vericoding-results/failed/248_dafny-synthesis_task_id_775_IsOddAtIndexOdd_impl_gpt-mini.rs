use vstd::prelude::*;

verus! {

spec fn is_odd(n: int) -> bool {
    n % 2 == 1
}

// <vc-helpers>
// No helpers needed for this proof.
// </vc-helpers>

// <vc-spec>
fn is_odd_at_index_odd(a: &[int]) -> (result: bool)
    ensures result <==> forall|i: int| 0 <= i < a.len() ==> (is_odd(i) ==> is_odd(a[i]))
// </vc-spec>
// <vc-code>
{
    let mut j: int = 0;
    let mut ok: bool = true;
    while j < a.len() as int
        invariant 0 <= j
        invariant j <= a.len() as int
        invariant ok == (forall |k: int| 0 <= k && k < j ==> (is_odd(k) ==> is_odd(a[k as usize])))
    {
        ok = ok && (!is_odd(j) || is_odd(a[j as usize]));
        j = j + 1;
    }
    result = ok;
}
// </vc-code>

fn main() {
}

}