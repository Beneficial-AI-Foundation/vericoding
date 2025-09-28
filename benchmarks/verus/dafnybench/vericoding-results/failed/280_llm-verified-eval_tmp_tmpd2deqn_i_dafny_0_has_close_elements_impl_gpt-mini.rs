use vstd::prelude::*;

verus! {

spec fn abs(x: int) -> int {
    if x < 0 { -x } else { x }
}

// <vc-helpers>
// <vc-helpers>
/* No helpers needed for this implementation. */
// </vc-helpers>
// </vc-helpers>

// <vc-spec>
fn has_close_elements(numbers: Seq<int>, threshold: int) -> (result: bool)
    ensures
        result <==> exists|i: int, j: int|
            0 <= i < numbers.len() &&
            0 <= j < numbers.len() &&
            i != j &&
            abs(numbers[i] - numbers[j]) < threshold,
        result ==> numbers.len() > 1,
// </vc-spec>
// <vc-code>
{
    let len: nat = numbers.len();

    if len <= 1 {
        return false;
    }

    let mut i: nat = 0;
    while i < len
        invariant i <= len;
        invariant forall|ii: int, jj: int|
            0 <= ii && ii < (i as int) &&
            0 <= jj && jj < (len as int) &&
            ii != jj ==>
                abs(numbers[@ii] - numbers[@jj]) >= threshold
            #[trigger abs(numbers[@ii] - numbers[@jj]) < threshold];
        decreases len - i;
    {
        let mut j: nat = i + 1;
        while j < len
            invariant i + 1 <= j && j <= len;
            invariant forall|jj: int|
                (i as int) < jj && jj < (j as int) ==>
                    abs(numbers[@(i as int)] - numbers[@jj]) >= threshold
                #[trigger abs(numbers[@(i as int)] - numbers[@jj]) < threshold];
            decreases len - j;
        {
            if abs(numbers[@(i as int)] - numbers[@(j as int)]) < threshold {
                proof {
                    assert(i < len);
                    assert(j < len);
                    assert(abs(numbers[@(i as int)] - numbers[@(j as int)]) < threshold);
                    assert(exists|ii: int, jj: int|
                        0 <= ii && ii < (len as int) &&
                        0 <= jj && jj < (len as int) &&
                        ii != jj &&
                        abs(numbers[@ii] - numbers[@jj]) < threshold
                    );
                }
                return true;
            }
            j = j + 1;
        }

        proof {
            // Combine the outer invariant (for ii < i) and the inner invariant (for ii == i against jj > i)
            // to produce the outer invariant for i+1.
            assert(forall|ii: int, jj: int|
                0 <= ii && ii < (i as int) &&
                0 <= jj && jj < (len as int) &&
                ii != jj ==>
                    abs(numbers[@ii] - numbers[@jj]) >= threshold
            );
            assert(forall|jj: int|
                (i as int) < jj && jj < (len as int) ==>
                    abs(numbers[@(i as int)] - numbers[@jj]) >= threshold
            );

            // Now prove: forall ii < i+1, forall jj < len, ii != jj ==> abs(...) >= threshold
            assert(forall|ii: int, jj: int|
                0 <= ii && ii < ((i + 1) as int) &&
                0 <= jj && jj < (len as int) &&
                ii != jj ==>
                    abs(numbers[@ii] - numbers[@jj]) >= threshold
            );
        }

        i = i + 1;
    }

    false
}
// </vc-code>

fn main() {}

}