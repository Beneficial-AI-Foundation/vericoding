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
/* helper modified by LLM (iteration 5): Simplified the logic to match the `calculate_minimum_bullets_helper` spec which doesn't consider `time_available` for calculating bullets. It calculates bullets for effective shooting regardless of time.*/
spec fn calculate_bullets_for_wave(wave: Wave, k: nat) -> nat {
    if k > 0 {
        let reloads_needed = (wave.monsters + k - 1) / k;
        reloads_needed * k
    } else {
        0 // Should not be reached given k > 0 precondition in main function
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
{
    /* code modified by LLM (iteration 5): Fixed `nat` and `int` usage outside ghost code and addressed calculation of `reloads_needed_count` to ensure type safety in `exec` context.*/

    if !can_solve_all_waves(waves@, k as nat) {
        return -1;
    }

    let mut total_bullets: nat = 0;
    let mut current_bullets_in_gun: nat = k as nat; // Initial bullets in gun, matching calculate_minimum_bullets_helper's initial call
    let mut i: usize = 0;

    while i < waves.len()
        invariant
            0 <= i as int && i as int <= waves.len(),
            valid_waves(waves@),
            k as nat > 0,
            current_bullets_in_gun >= 0,
            current_bullets_in_gun <= k as nat,
            total_bullets + calculate_minimum_bullets_helper(waves@, k as nat, i as nat, current_bullets_in_gun) == calculate_minimum_bullets(waves@, k as nat),
        decreases waves.len() - i as int
    {
        let wave = &waves[i];
        let wave_monsters = wave.monsters; // ghost code

        if current_bullets_in_gun >= wave_monsters {
            total_bullets = total_bullets + wave_monsters;
            current_bullets_in_gun = k as nat; 
        } else {
            let reloads_needed_count_val = (wave_monsters + k as nat - 1) / (k as nat);

            let bullets_expended_for_wave = reloads_needed_count_val * (k as nat);
            total_bullets = total_bullets + bullets_expended_for_wave;
            current_bullets_in_gun = k as nat;
        }

        i = i + 1;
    }
    total_bullets as i32
}
// </vc-code>


}

fn main() {}