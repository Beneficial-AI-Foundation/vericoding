use vstd::prelude::*;

verus! {

// <vc-helpers>
// <vc-helpers>
// No helper lemmas required for this proof.
 // </vc-helpers>
// </vc-helpers>

// <vc-spec>
fn rotate_right(l: Seq<int>, n: int) -> (r: Seq<int>)
    requires n >= 0,
    ensures 
        r.len() == l.len(),
        forall|i: int| 0 <= i < l.len() ==> r.index(i) == l.index((i - n + l.len() as int) % l.len() as int),
// </vc-spec>
// <vc-code>
{
    if l.len() == 0 {
        return Vec::<int>::new().into_seq();
    }

    let len: nat = l.len();
    let d: int = len as int;
    let mut v: Vec<int> = Vec::new();

    let mut i: nat = 0;
    while i < len
        invariant i <= len;
        invariant v.len() == i;
        invariant forall|j: nat| j < i ==> v.index(j) == l.index(((j as int - n + d) % d) as nat);
    {
        let src_int: int = ((i as int - n + d) % d);
        // modulo with positive divisor yields 0 <= src_int < d
        assert(src_int >= 0);
        assert(src_int < d);
        let src: nat = src_int as nat;
        let x: int = l.index(src);
        v.push(x);
        i = i + 1;
    }

    let r: Seq<int> = v.into_seq();

    proof {
        // From the loop invariant at i == len we get the required forall property.
        assert(r.len() == len);
        assert(forall(|j: int| 0 <= j && j < len as int ==>
            #[trigger] r.index(j as nat) == l.index(((j - n + d) % d) as nat)));
    }

    r
}
// </vc-code>

fn main() {}

}