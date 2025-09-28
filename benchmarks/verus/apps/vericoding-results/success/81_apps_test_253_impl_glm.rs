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
fn min_i8(a: i8, b: i8) -> i8 {
    if a < b { a } else { b }
}

fn max_i8(a: i8, b: i8) -> i8 {
    if a > b { a } else { b }
}
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
    /* code modified by LLM (iteration 3): fixed sorting logic to match sort_three spec function */
    let x = nums[0];
    let y = nums[1];
    let z = nums[2];

    let a;
    let b;
    let c;
    if x <= y && x <= z {
        a = x;
        if y <= z {
            b = y;
            c = z;
        } else {
            b = z;
            c = y;
        }
    } else if y <= x && y <= z {
        a = y;
        if x <= z {
            b = x;
            c = z;
        } else {
            b = z;
            c = x;
        }
    } else {
        a = z;
        if x <= y {
            b = x;
            c = y;
        } else {
            b = y;
            c = x;
        }
    }

    if a > 3i8 {
        vec!['N', 'O']
    } else if a == 3i8 {
        if b > 3i8 {
            vec!['N', 'O']
        } else if b == 3i8 {
            if c > 3i8 {
                vec!['N', 'O']
            } else {
                vec!['Y', 'E', 'S']
            }
        } else {
            vec!['N', 'O']
        }
    } else if a == 1i8 {
        vec!['Y', 'E', 'S']
    } else {
        if b == 2i8 {
            vec!['Y', 'E', 'S']
        } else if b > 4i8 {
            vec!['N', 'O']
        } else if b == 4i8 {
            if c == 4i8 {
                vec!['Y', 'E', 'S']
            } else {
                vec!['N', 'O']
            }
        } else {
            vec!['N', 'O']
        }
    }
}
// </vc-code>


}

fn main() {}