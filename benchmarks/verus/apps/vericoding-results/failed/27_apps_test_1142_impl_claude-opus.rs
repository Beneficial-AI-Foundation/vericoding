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
    /* code modified by LLM (iteration 5): Removed unnecessary nat to u32 casts - Wave fields are already usable as u32 in exec context */
    let mut wave_idx: usize = 0;
    let mut total_bullets: u32 = 0;
    let mut current_bullets: u32 = k as u32;
    let mut last_end_time: u32 = 0;
    
    while wave_idx < waves.len()
        invariant
            wave_idx <= waves.len(),
            k > 0,
            current_bullets <= k as u32,
            valid_waves(waves@),
            wave_idx > 0 ==> last_end_time == waves[wave_idx - 1].end_time,
            forall|j: int| 0 <= j < wave_idx ==> can_solve_wave(waves@, j as nat, k as nat),
    {
        let wave = &waves[wave_idx];
        
        // Check if we can reach this wave in time after reloading from previous wave
        if wave_idx > 0 {
            let time_gap = wave.start_time - last_end_time;
            let prev_wave = &waves[wave_idx - 1];
            let reloads_needed = if prev_wave.monsters <= k as u32 {
                0u32
            } else {
                (prev_wave.monsters - 1) / (k as u32)
            };
            
            if reloads_needed > time_gap {
                return -1;
            }
            current_bullets = k as u32;
        }
        
        // Check if we can defeat all monsters in this wave
        let time_available = wave.end_time - wave.start_time + 1;
        let max_possible_shots = time_available * (k as u32);
        
        if wave.monsters > max_possible_shots {
            return -1;
        }
        
        // Calculate bullets needed for this wave
        if current_bullets >= wave.monsters {
            total_bullets = total_bullets + wave.monsters;
            current_bullets = k as u32;
        } else {
            let full_reloads = wave.monsters / (k as u32);
            let remainder = wave.monsters % (k as u32);
            let bullets_used = if remainder == 0 {
                full_reloads * (k as u32)
            } else {
                (full_reloads + 1) * (k as u32)
            };
            total_bullets = total_bullets + bullets_used;
            current_bullets = k as u32;
        }
        
        last_end_time = wave.end_time;
        wave_idx = wave_idx + 1;
    }
    
    total_bullets as i32
}
// </vc-code>


}

fn main() {}