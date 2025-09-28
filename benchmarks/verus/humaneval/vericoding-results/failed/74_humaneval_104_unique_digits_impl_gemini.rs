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
#[verifier::spinoff_prover]
fn compute_has_no_even_digit(n: u8) -> (b: bool)
    ensures b == has_no_even_digit(n as int)
    decreases n
{
    if n < 10 {
        (n % 2) == 1
    } else {
        if (n % 2) == 0 {
            false
        } else {
            compute_has_no_even_digit(n / 10)
        }
    }
}

fn contains(v: &Vec<u8>, e: u8) -> (b: bool)
    ensures b == v@.contains(e)
{
    let mut i = 0;
    while i < v.len()
        invariant
            forall|k: int| 0 <= k < i ==> v@[k] != e,
        decreases v.len() - i
    {
        if v[i] == e {
            return true;
        }
        i += 1;
    }
    false
}

fn insert_sorted(v: &mut Vec<u8>, e: u8)
    requires
        forall|i: int, j: int| 0 <= i < j < old(v)@.len() ==> old(v)@[i] <= old(v)@[j],
    ensures
        v@.len() == old(v)@.len() + 1,
        v@.to_multiset() == old(v)@.to_multiset().insert(e),
        forall|i: int, j: int| 0 <= i < j < v@.len() ==> v@[i] <= v@[j],
{
    let mut i: usize = 0;
    while i < v.len() && v[i] < e
        invariant
            0 <= i <= v.len(),
            v@ == old(v)@,
            forall|k: int| 0 <= k < i as int ==> v@[k] < e,
        decreases v.len() - i
    {
        i += 1;
    }
    v.insert(i, e);
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
    /* code modified by LLM (iteration 2): fix type error in loop invariant by casting usize to int */
    let mut result: Vec<u8> = Vec::new();
    let mut i = 0;
    while i < x.len()
        invariant
            0 <= i <= x.len(),
            forall|ii: int, jj: int| 0 <= ii < jj < result@.len() ==> result@[ii] <= result@[jj],
            forall|e: u8| result@.contains(e) ==> has_no_even_digit(e as int),
            forall|e: u8| result@.contains(e) ==> x@.subrange(0, i as int).contains(e),
            forall|e: u8| x@.subrange(0, i as int).contains(e) && has_no_even_digit(e as int) ==> result@.contains(e),
        decreases x.len() - i
    {
        let e = x[i];
        if compute_has_no_even_digit(e) {
            if !contains(&result, e) {
                insert_sorted(&mut result, e);
            }
        }
        i += 1;
    }
    result
}
// </vc-code>


}

fn main() {}