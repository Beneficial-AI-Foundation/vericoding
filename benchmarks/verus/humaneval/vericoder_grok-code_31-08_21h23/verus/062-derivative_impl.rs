use vstd::prelude::*;

verus! {

// <vc-helpers>
#[verifier::spec]
fn map_values<T, U>(s: Seq<T>, f: FnSpec(T) -> U) -> Seq<U> {
    s.map(|_, x| f(x))
}
// </vc-helpers>

// <vc-spec>
fn derivative(xs: &Vec<usize>) -> (ret: Option<Vec<usize>>)
    // post-conditions-start
    ensures
        ret.is_some() ==> xs@.len() == 0 || xs@.map(|i: int, x| i * x).skip(1)
            =~= ret.unwrap()@.map_values(|x| x as int),
    // post-conditions-end
// </vc-spec>
// <vc-code>
{
    if (xs.len() == 0) {
        let mut result = Vec::new();
        Some(result)
    } else {
        let len = xs.len();
        let mut result = Vec::new();
        let mut i: usize = 1;
        while (i < len)
            invariant
                i >= 1,
                i <= len,
                result@.len() == (i - 1) as int,
                forall |k: nat| #[trigger] result@[k as int] , k < result@.len() ==> result@[k as int] as int == ((k + 1) as int) * (xs@[(k + 1) as int] as int)
            decreases len - i
        {
            let val = ((i as u64) * (xs[i] as u64)) as usize;
            result.push(val);
            proof {
                assert(result@[((i - 1) as int)] as int == ((i as int)) * (xs@[i as int] as int));
            }
            i += 1;
        }
        assert(result@.map(|_, x| x as int) =~= xs@.map(|i: int, x: usize| i as int * x as int).skip(1));
        Some(result)
    }
}
// </vc-code>

fn main() {}
}