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
/* helper modified by LLM (iteration 3): exec sorter over i8 with spec-level ensures tying to sort_three over ints */
fn sort_three_exec(x: i8, y: i8, z: i8) -> (result: (i8, i8, i8))
    ensures
        (result.0 as int, result.1 as int, result.2 as int) == sort_three(x as int, y as int, z as int),
{
    if x <= y && x <= z {
        if y <= z { (x, y, z) } else { (x, z, y) }
    } else if y <= x && y <= z {
        if x <= z { (y, x, z) } else { (y, z, x) }
    } else {
        if x <= y { (z, x, y) } else { (z, y, x) }
    }
}

/* helper modified by LLM (iteration 3): constructor for YES */
fn make_yes() -> (result: Vec<char>)
    ensures
        result@ == seq!['Y', 'E', 'S'],
{
    let mut v: Vec<char> = Vec::new();
    v.push('Y');
    v.push('E');
    v.push('S');
    v
}

/* helper modified by LLM (iteration 3): constructor for NO */
fn make_no() -> (result: Vec<char>)
    ensures
        result@ == seq!['N', 'O'],
{
    let mut v: Vec<char> = Vec::new();
    v.push('N');
    v.push('O');
    v
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
    /* code modified by LLM (iteration 3): avoid exec ints; sort i8s, mirror spec logic, and prove correspondence */
    proof {
        assert(valid_input(nums@.map(|i, x| x as int)));
        assert(nums@.len() == 3);
        assert(nums.len() == nums@.len());
        assert(nums.len() == 3);
        assert(0 < nums.len());
        assert(1 < nums.len());
        assert(2 < nums.len());
    }

    let x_i8 = nums[0];
    let y_i8 = nums[1];
    let z_i8 = nums[2];

    let (a, b, c) = sort_three_exec(x_i8, y_i8, z_i8);

    proof {
        reveal(sort_three);
        reveal(compute_result);
    }

    let result: Vec<char>;

    if a > 3i8 {
        result = make_no();
        proof {
            let aa: int = a as int; let bb: int = b as int; let cc: int = c as int;
            assert((aa, bb, cc) == sort_three(x_i8 as int, y_i8 as int, z_i8 as int));
            assert(aa > 3);
            assert(compute_result(x_i8 as int, y_i8 as int, z_i8 as int) == seq!['N', 'O']);
        }
    } else if a == 3i8 {
        if b > 3i8 {
            result = make_no();
            proof {
                let aa: int = a as int; let bb: int = b as int; let cc: int = c as int;
                assert((aa, bb, cc) == sort_three(x_i8 as int, y_i8 as int, z_i8 as int));
                assert(aa == 3);
                assert(bb > 3);
                assert(compute_result(x_i8 as int, y_i8 as int, z_i8 as int) == seq!['N', 'O']);
            }
        } else if b == 3i8 {
            if c > 3i8 {
                result = make_no();
                proof {
                    let aa: int = a as int; let bb: int = b as int; let cc: int = c as int;
                    assert((aa, bb, cc) == sort_three(x_i8 as int, y_i8 as int, z_i8 as int));
                    assert(aa == 3);
                    assert(bb == 3);
                    assert(cc > 3);
                    assert(compute_result(x_i8 as int, y_i8 as int, z_i8 as int) == seq!['N', 'O']);
                }
            } else {
                result = make_yes();
                proof {
                    let aa: int = a as int; let bb: int = b as int; let cc: int = c as int;
                    assert((aa, bb, cc) == sort_three(x_i8 as int, y_i8 as int, z_i8 as int));
                    assert(aa == 3);
                    assert(bb == 3);
                    assert(!(cc > 3));
                    assert(compute_result(x_i8 as int, y_i8 as int, z_i8 as int) == seq!['Y', 'E', 'S']);
                }
            }
        } else {
            result = make_no();
            proof {
                let aa: int = a as int; let bb: int = b as int; let cc: int = c as int;
                assert((aa, bb, cc) == sort_three(x_i8 as int, y_i8 as int, z_i8 as int));
                assert(aa == 3);
                assert(!(bb > 3));
                assert(!(bb == 3));
                assert(compute_result(x_i8 as int, y_i8 as int, z_i8 as int) == seq!['N', 'O']);
            }
        }
    } else if a == 1i8 {
        result = make_yes();
        proof {
            let aa: int = a as int; let bb: int = b as int; let cc: int = c as int;
            assert((aa, bb, cc) == sort_three(x_i8 as int, y_i8 as int, z_i8 as int));
            assert(aa == 1);
            assert(compute_result(x_i8 as int, y_i8 as int, z_i8 as int) == seq!['Y', 'E', 'S']);
        }
    } else {
        if b == 2i8 {
            result = make_yes();
            proof {
                let aa: int = a as int; let bb: int = b as int; let cc: int = c as int;
                assert((aa, bb, cc) == sort_three(x_i8 as int, y_i8 as int, z_i8 as int));
                assert(!(aa > 3));
                assert(aa != 3);
                assert(aa != 1);
                assert(bb == 2);
                assert(compute_result(x_i8 as int, y_i8 as int, z_i8 as int) == seq!['Y', 'E', 'S']);
            }
        } else if b > 4i8 {
            result = make_no();
            proof {
                let aa: int = a as int; let bb: int = b as int; let cc: int = c as int;
                assert((aa, bb, cc) == sort_three(x_i8 as int, y_i8 as int, z_i8 as int));
                assert(!(aa > 3));
                assert(aa != 3);
                assert(aa != 1);
                assert(bb > 4);
                assert(compute_result(x_i8 as int, y_i8 as int, z_i8 as int) == seq!['N', 'O']);
            }
        } else if b == 4i8 {
            if c == 4i8 {
                result = make_yes();
                proof {
                    let aa: int = a as int; let bb: int = b as int; let cc: int = c as int;
                    assert((aa, bb, cc) == sort_three(x_i8 as int, y_i8 as int, z_i8 as int));
                    assert(!(aa > 3));
                    assert(aa != 3);
                    assert(aa != 1);
                    assert(bb == 4);
                    assert(cc == 4);
                    assert(compute_result(x_i8 as int, y_i8 as int, z_i8 as int) == seq!['Y', 'E', 'S']);
                }
            } else {
                result = make_no();
                proof {
                    let aa: int = a as int; let bb: int = b as int; let cc: int = c as int;
                    assert((aa, bb, cc) == sort_three(x_i8 as int, y_i8 as int, z_i8 as int));
                    assert(!(aa > 3));
                    assert(aa != 3);
                    assert(aa != 1);
                    assert(bb == 4);
                    assert(cc != 4);
                    assert(compute_result(x_i8 as int, y_i8 as int, z_i8 as int) == seq!['N', 'O']);
                }
            }
        } else {
            result = make_no();
            proof {
                let aa: int = a as int; let bb: int = b as int; let cc: int = c as int;
                assert((aa, bb, cc) == sort_three(x_i8 as int, y_i8 as int, z_i8 as int));
                assert(!(aa > 3));
                assert(aa != 3);
                assert(aa != 1);
                assert(!(bb == 2));
                assert(!(bb > 4));
                assert(!(bb == 4));
                assert(compute_result(x_i8 as int, y_i8 as int, z_i8 as int) == seq!['N', 'O']);
            }
        }
    }

    proof {
        assert(nums@.len() == nums.len());
        assert(nums.len() == 3);
        assert(0 < nums.len());
        assert(1 < nums.len());
        assert(2 < nums.len());
        assert(nums@[0] == nums[0]);
        assert(nums@[1] == nums[1]);
        assert(nums@[2] == nums[2]);
        assert(compute_result(x_i8 as int, y_i8 as int, z_i8 as int)
            == compute_result(nums@[0] as int, nums@[1] as int, nums@[2] as int));
    }

    result
}
// </vc-code>


}

fn main() {}