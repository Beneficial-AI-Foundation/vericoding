use vstd::prelude::*;

verus! {

spec fn semi_ordered_permutation_precond(nums: Seq<int>) -> bool {
    true
}

spec fn index_of_seq(nums: Seq<int>, target: int) -> int
    decreases nums.len(),
{
    if nums.len() == 0 {
        0
    } else if nums[0] == target {
        0
    } else {
        1 + index_of_seq(nums.subrange(1, nums.len() as int), target)
    }
}

spec fn semi_ordered_permutation_postcond(nums: Seq<int>, result: int) -> bool {
    let n = nums.len();
    let pos1 = index_of_seq(nums, 1);
    let posn = index_of_seq(nums, n as int);
    if pos1 > posn {
        pos1 + n == result + 2 + posn
    } else {
        pos1 + n == result + 1 + posn
    }
}

fn semi_ordered_permutation(nums: Vec<i32>) -> (result: i32)
    requires
        nums.len() > 0,
        nums.len() <= 1000,
        semi_ordered_permutation_precond(nums@.map(|i, x| x as int)),
    ensures
        semi_ordered_permutation_postcond(nums@.map(|i, x| x as int), result as int),
{
    let length_list = nums.len();
    let num_one: i32 = 1;
    let largest_num: i32 = length_list as i32;

    let first_index = index_of_exec(&nums, num_one) as i32;
    let last_index = index_of_exec(&nums, largest_num) as i32;

    let start_position: i32 = 0;
    let end_position: i32 = (length_list as i32) - 1;

    let should_move_one = first_index != start_position;
    let should_move_last = last_index != end_position;

    let distance_one = if should_move_one { first_index } else { 0 };
    let distance_last = if should_move_last { 
        if end_position >= last_index {
            end_position - last_index 
        } else {
            0
        }
    } else { 0 };

    let total_moves = if distance_one >= 0 && distance_last >= 0 && 
                         distance_one <= 1000 && distance_last <= 1000 {
        distance_one + distance_last
    } else {
        0
    };
    
    let need_adjustment = first_index > last_index;
    let adjusted_moves = if need_adjustment && total_moves > 0 { 
        total_moves - 1 
    } else { 
        total_moves 
    };

    adjusted_moves
}

fn index_of_exec(nums: &Vec<i32>, target: i32) -> (result: usize)
    requires
        nums.len() > 0,
    ensures
        result < nums.len(),
{
    let mut i: usize = 0;
    while i < nums.len()
        invariant
            0 <= i <= nums.len(),
        decreases
            nums.len() - i,
    {
        if nums[i] == target {
            return i;
        }
        i += 1;
    }
    0
}

proof fn semi_ordered_permutation_spec_satisfied(nums: Seq<int>, result: int)
    requires
        nums.len() > 0,
        nums.len() <= 1000,
        semi_ordered_permutation_precond(nums),
    ensures
        semi_ordered_permutation_postcond(nums, result) ==> 
            semi_ordered_permutation_postcond(nums, result),
{
    // proof skeleton - to be completed
}

}

fn main() {}