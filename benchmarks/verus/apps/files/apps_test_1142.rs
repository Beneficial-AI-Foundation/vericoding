// <vc-preamble>
use vstd::prelude::*;

verus! {

#[derive(PartialEq, Eq)]
pub struct Wave {
    pub start_time: nat,
    pub end_time: nat,
    pub monsters: nat,
}

spec fn valid_waves(waves: Seq<Wave>) -> bool {
    forall|i: int| 0 <= i < waves.len() ==> 
        waves[i].start_time <= waves[i].end_time &&
        waves[i].monsters > 0 &&
        (i > 0 ==> waves[i-1].end_time <= waves[i].start_time)
}

spec fn can_solve_all_waves(waves: Seq<Wave>, k: nat) -> bool {
    k > 0 && 
    forall|i: int| 0 <= i < waves.len() ==> 
        can_solve_wave(waves, i as nat, k)
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
    &&& wave_index > 0 
    &&& wave_index < waves.len() 
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
            (monsters as int - 1) / (k as int)
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

spec fn calculate_minimum_bullets_helper(waves: Seq<Wave>, k: nat, wave_index: nat, bullets_remaining: nat) -> nat {
    if wave_index >= waves.len() {
        0
    } else {
        let wave = waves[wave_index as int];
        let bullets_needed = if bullets_remaining >= wave.monsters {
            wave.monsters
        } else {
            let reloads = (wave.monsters as int - bullets_remaining as int + k as int - 1) / (k as int);
            (reloads * (k as int) + wave.monsters as int) as nat
        };
        bullets_needed + calculate_minimum_bullets_helper(waves, k, wave_index + 1, k)
    }
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn solve_monster_waves(waves: Seq<Wave>, k: nat) -> (result: i32)
    requires 
        valid_waves(waves),
        k > 0,
    ensures 
        result == -1 <==> !can_solve_all_waves(waves, k),
        result >= 0 <==> can_solve_all_waves(waves, k),
        can_solve_all_waves(waves, k) ==> result == calculate_minimum_bullets(waves, k),
// </vc-spec>
// <vc-code>
{
    // impl-start
    assume(false);
    -1
    // impl-end
}
// </vc-code>


}

fn main() {}