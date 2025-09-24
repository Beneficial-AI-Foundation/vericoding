// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn valid_input(nums: Seq<int>) -> bool {
    nums.len() == 3 &&
    forall|i: int| 0 <= i < nums.len() ==> nums[i] > 0 &&
    forall|i: int| 0 <= i < nums.len() ==> nums[i] <= 1500
}

spec fn sort_three(x: int, y: int, z: int) -> (int, int, int) {
    if x <= y && x <= z {
        if y <= z { (x, y, z) } else { (x, z, y) }
    } else if y <= x && y <= z {
        if x <= z { (y, x, z) } else { (y, z, x) }
    } else {
        if x <= y { (z, x, y) } else { (z, y, x) }
    }
}

spec fn compute_result(x: int, y: int, z: int) -> Seq<char> {
    let sorted = sort_three(x, y, z);
    let a = sorted.0;
    let b = sorted.1;
    let c = sorted.2;

    if a > 3 {
        seq!['N', 'O']
    } else if a == 3 {
        if b > 3 {
            seq!['N', 'O']
        } else if b == 3 {
            if c > 3 { seq!['N', 'O'] } else { seq!['Y', 'E', 'S'] }
        } else {
            seq!['N', 'O']
        }
    } else if a == 1 {
        seq!['Y', 'E', 'S']
    } else {
        if b == 2 {
            seq!['Y', 'E', 'S']
        } else if b > 4 {
            seq!['N', 'O']
        } else if b == 4 {
            if c == 4 { seq!['Y', 'E', 'S'] } else { seq!['N', 'O'] }
        } else {
            seq!['N', 'O']
        }
    }
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn solve(nums: Vec<i8>) -> (result: Vec<char>)
    requires
        valid_input(nums@.map(|i, x| x as int)),
    ensures
        result@ == seq!['Y', 'E', 'S'] || result@ == seq!['N', 'O'],
        result@ == compute_result(nums@[0] as int, nums@[1] as int, nums@[2] as int),
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>


}

fn main() {}