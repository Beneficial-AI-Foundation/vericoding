// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn has_no_even_digit(n: int) -> bool
  decreases n
{
  n >= 0 && ((n < 10 && n % 2 == 1) || (n % 2 == 1 && has_no_even_digit(n / 10)))
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): executable predicate aligned with spec; moved all 'int' uses into proof blocks */
fn has_no_even_digit_exec(b: u8) -> (r: bool)
    ensures
        r == has_no_even_digit(b as int),
    decreases b as int
{
    if b < 10 {
        let r0 = b % 2 == 1;
        proof {
            let ni: int = b as int;
            assert(has_no_even_digit(ni) == (ni >= 0 && ((ni < 10int && ni % 2int == 1int) || (ni % 2int == 1int && has_no_even_digit(ni / 10int)))));
            assert(ni >= 0);
            assert(ni < 10int);
            assert(ni / 10int == 0int);
            if r0 {
                assert(ni % 2int == 1int);
                assert(has_no_even_digit(ni));
            } else {
                assert(!(ni % 2int == 1int));
                assert(!has_no_even_digit(ni));
            }
            assert(r0 == has_no_even_digit(ni));
        }
        r0
    } else {
        let rec = has_no_even_digit_exec(b / 10);
        let r0 = (b % 2 == 1) && rec;
        proof {
            let ni: int = b as int;
            assert(has_no_even_digit(ni) == (ni >= 0 && ((ni < 10int && ni % 2int == 1int) || (ni % 2int == 1int && has_no_even_digit(ni / 10int)))));
            assert(ni >= 0);
            assert(!(ni < 10int));
            assert(ni / 10int == (b / 10) as int);
            assert(rec == has_no_even_digit((b / 10) as int));
            assert(rec == has_no_even_digit(ni / 10int));
            if r0 {
                assert(b % 2 == 1);
                assert(ni % 2int == 1int);
                assert(has_no_even_digit(ni / 10int));
                assert(has_no_even_digit(ni));
            } else {
                if !(b % 2 == 1) {
                    assert(!(ni % 2int == 1int));
                    assert(!has_no_even_digit(ni));
                } else {
                    assert(b % 2 == 1);
                    assert(!rec);
                    assert(!has_no_even_digit(ni / 10int));
                    assert(!has_no_even_digit(ni));
                }
            }
            assert(r0 == has_no_even_digit(ni));
        }
        r0
    }
}

/* helper modified by LLM (iteration 5): executable membership check with spec correspondence */
fn vec_contains(x: &Vec<u8>, e: u8) -> (r: bool)
    ensures
        r == x@.contains(e)
{
    let mut i: usize = 0;
    let mut found: bool = false;
    while i < x.len()
        invariant
            i <= x.len(),
            (i as int) <= x@.len(),
            found ==> exists|k: int| 0 <= k < i as int && x@[k] == e,
            !found ==> forall|k: int| 0 <= k < i as int ==> x@[k] != e,
        decreases (x.len() - i) as int
    {
        if x[i] == e {
            found = true;
        }
        i += 1;
    }
    found
}
// </vc-helpers>

// <vc-spec>
fn unique_digits(x: Vec<u8>) -> (result: Vec<u8>)
  ensures 
    forall|i: int| 0 <= i < result@.len() ==> has_no_even_digit(result@[i] as int) &&
    forall|i: int, j: int| 0 <= i < j < result@.len() ==> result@[i] <= result@[j] &&
    forall|e: u8| x@.contains(e) && has_no_even_digit(e as int) ==> result@.contains(e) &&
    forall|e: u8| result@.contains(e) ==> x@.contains(e)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): simplify loop invariant to track 'already collected or not yet processed', keeping ascending order by scanning in increasing u8 order */
    let mut result: Vec<u8> = Vec::new();
    let mut p: usize = 0;
    while p <= 255usize
        invariant
            p <= 256usize,
            forall|i: int| 0 <= i < result@.len() ==> has_no_even_digit(result@[i] as int),
            forall|i: int, j: int| 0 <= i < j < result@.len() ==> result@[i] <= result@[j],
            forall|e: u8| result@.contains(e) ==> x@.contains(e),
            forall|e: u8| x@.contains(e) && has_no_even_digit(e as int) ==> result@.contains(e) || (e as int) >= p as int,
            forall|i: int| 0 <= i < result@.len() ==> (result@[i] as int) <= p as int,
        decreases (256usize - p) as int
    {
        let e: u8 = p as u8;
        let pred = has_no_even_digit_exec(e);
        let present = vec_contains(&x, e);
        if pred && present {
            result.push(e);
        }
        p += 1;
    }
    result
}
// </vc-code>


}

fn main() {}