use vstd::prelude::*;

verus! {

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
proof fn intersperse(numbers: Seq<int>, delimiter: int) -> (interspersed: Seq<int>)
    ensures
        interspersed.len() == if numbers.len() > 0 { 2 * numbers.len() - 1 } else { 0 },
        forall|i: int| 0 <= i < interspersed.len() && i % 2 == 0 ==> 
            interspersed[i] == numbers[i / 2],
        forall|i: int| 0 <= i < interspersed.len() && i % 2 == 1 ==>
            interspersed[i] == delimiter,
// </vc-spec>
// <vc-code>
{
    if numbers.len() == 0 {
        Seq::empty()
    } else {
        let n = numbers.len();
        let len = 2 * n - 1;
        Seq::new(len as nat, |i| {
            let i_int = i as int;
            if i_int % 2 == 0 {
                numbers[i_int / 2]
            } else {
                delimiter
            }
        })
    }
}
// </vc-code>

fn main() {}

}