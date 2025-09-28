// <vc-preamble>
use vstd::prelude::*;

verus! {
#[derive(PartialEq, Eq)]
struct Wave {
    start_time: nat,
    end_time: nat,
    monsters: nat,
}

spec fn valid_waves(waves: Seq<Wave>) -> bool {
    forall|i: int| 0 <= i < waves.len() ==> 
        #[trigger] waves[i].start_time <= waves[i].end_time &&
        waves[i].monsters > 0 &&
        (i > 0 ==> waves[i-1].end_time <= waves[i].start_time)
}

spec fn can_solve_all_waves(waves: Seq<Wave>, k: nat) -> bool {
    k > 0 && 
    forall|i: int| 0 <= i < waves.len() ==> 
        #[trigger] can_solve_wave(waves, i as nat, k)
}

spec fn can_solve_wave(waves: Seq<Wave>, wave_index: nat, k: nat) -> bool {
    &&& wave_index < waves.len()
    &&& k > 0
    &&& {
        let wave = waves[wave_index as int];
        let time_available = wave.end_time - wave.start_time + 1;
        let max_possible_shots = time_available * k;
        wave.monsters <= max_possible_shots &&
        (wave_index == 0 || can_reach_wave_in_time(waves, wave_index, k))
    }
}

spec fn can_reach_wave_in_time(waves: Seq<Wave>, wave_index: nat, k: nat) -> bool {
    &&& wave_index > 0 && wave_index < waves.len()
    &&& k > 0
    &&& {
        let prev_wave = waves[wave_index as int - 1];
        let curr_wave = waves[wave_index as int];
        let time_gap = curr_wave.start_time - prev_wave.end_time;
        let reloads_needed = calculate_reloads_needed(prev_wave.monsters, k);
        reloads_needed <= time_gap
    }
}

spec fn calculate_reloads_needed(monsters: nat, k: nat) -> nat {
    if k > 0 {
        if monsters <= k { 
            0 
        } else { 
            ((monsters - 1) as int / k as int) as nat
        }
    } else {
        0
    }
}

spec fn calculate_minimum_bullets(waves: Seq<Wave>, k: nat) -> nat {
    if k > 0 && valid_waves(waves) && can_solve_all_waves(waves, k) {
        calculate_minimum_bullets_helper(waves, k, 0, k)
    } else {
        0
    }
}

spec fn calculate_minimum_bullets_helper(waves: Seq<Wave>, k: nat, wave_index: nat, current_bullets: nat) -> nat
    decreases waves.len() - wave_index
{
    if wave_index >= waves.len() {
        0
    } else {
        let wave = waves[wave_index as int];
        if current_bullets >= wave.monsters {
            wave.monsters + calculate_minimum_bullets_helper(waves, k, wave_index + 1, k)
        } else {
            let reloads_needed = (((wave.monsters - 1) as int / k as int) + 1) as nat;
            reloads_needed * k + calculate_minimum_bullets_helper(waves, k, wave_index + 1, k)
        }
    }
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 4): cast ghost nat fields to u64 for exec calculations to avoid spec type errors */
fn can_solve_wave_condition(waves: &Vec<Wave>, wave_index: usize, k: u8) -> (result: bool)
    requires
        wave_index < waves@.len(),
        k > 0,
    ensures
        result <==> can_solve_wave(waves@, wave_index as nat, k as nat),
{
    let wave = &waves[wave_index];
    let time_available = (wave.end_time as u64) - (wave.start_time as u64) + 1;
    let max_shots = time_available * (k as u64);
    let can_solve_current = (wave.monsters as u64) <= max_shots;
    if !can_solve_current {
        false
    } else if wave_index == 0 {
        true
    } else {
        let prev_wave = &waves[wave_index - 1];
        let gap = (wave.start_time as u64) - (prev_wave.end_time as u64);
        let reloads_needed = if (prev_wave.monsters as u64) <= (k as u64) {
            0
        } else {
            ((prev_wave.monsters as u64 - 1) / (k as u64))
        };
        reloads_needed <= gap
    }
}

/* helper modified by LLM (iteration 4): no changes needed */
fn can_solve_all_exec(waves: &Vec<Wave>, k: u8) -> (result: bool)
    requires
        k > 0,
    ensures
        result == can_solve_all_waves(waves@, k as nat),
{
    let mut i = 0;
    while i < waves.len()
        invariant
            forall|j: int| 0 <= j < i ==> can_solve_wave(waves@, j as nat, k as nat),
            i <= waves.len(),
        decreases waves.len() - i
    {
        if !can_solve_wave_condition(waves, i, k) {
            return false;
        }
        i += 1;
    }
    true
}

/* helper modified by LLM (iteration 4): no changes needed */
fn calculate_min_bullets_exec(waves: &Vec<Wave>, k: u64, wave_index: usize, current_bullets: u64) -> (result: u64)
    requires
        valid_waves(waves@),
        wave_index <= waves.len(),
        current_bullets == k,
        k > 0,
        can_solve_all_waves(waves@, k as nat),
    ensures
        result == calculate_minimum_bullets_helper(waves@, k as nat, wave_index as nat, current_bullets as nat),
    decreases waves.len() - wave_index
{
    if wave_index >= waves.len() {
        0
    } else {
        let wave = &waves[wave_index];
        if current_bullets >= (wave.monsters as u64) {
            (wave.monsters as u64) + calculate_min_bullets_exec(waves, k, wave_index + 1, k)
        } else {
            let reloads_needed = if (wave.monsters as u64) <= k {
                0
            } else {
                ((wave.monsters as u64 - 1) / k) + 1
            };
            (reloads_needed * k) + calculate_min_bullets_exec(waves, k, wave_index + 1, k)
        }
    }
}
// </vc-helpers>

// <vc-spec>
fn solve_monster_waves(waves: Vec<Wave>, k: u8) -> (result: i32)
    requires 
        valid_waves(waves@),
        k > 0,
    ensures 
        result == -1 <==> !can_solve_all_waves(waves@, k as nat),
        result >= 0 <==> can_solve_all_waves(waves@, k as nat),
        can_solve_all_waves(waves@, k as nat) ==> result == calculate_minimum_bullets(waves@, k as nat) as i32,
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 4): no changes needed */
{
    if !can_solve_all_exec(&waves, k) {
        return -1;
    }
    let total = calculate_min_bullets_exec(&waves, k as u64, 0, k as u64);
    return total as i32;
}
// </vc-code>


}

fn main() {}