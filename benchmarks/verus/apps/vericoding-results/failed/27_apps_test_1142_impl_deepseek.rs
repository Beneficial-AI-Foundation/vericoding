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
/* helper modified by LLM (iteration 5): Fixed ghost_closure macro issue and added proper ghost function */
proof fn check_can_solve_all_waves(waves: Seq<Wave>, k: nat) -> (result: bool)
    requires
        k > 0,
    ensures
        result == can_solve_all_waves(waves, k)
{
    result = can_solve_all_waves(waves, k);
}

fn calculate_reloads_needed_exec(monsters: u32, k: u32) -> u32
    requires
        k > 0,
    ensures
        result == (if monsters <= k { 0 } else { ((monsters - 1) / k) })
{
    if monsters <= k {
        0
    } else {
        (monsters - 1) / k
    }
}

proof fn can_reach_wave_in_time_lemma(waves: Seq<Wave>, wave_index: nat, k: nat)
    requires
        valid_waves(waves),
        wave_index > 0 && wave_index < waves.len(),
        k > 0,
        can_solve_wave(waves, wave_index, k),
    ensures
        can_reach_wave_in_time(waves, wave_index, k)
{
}

proof fn can_solve_wave_implies_valid(waves: Seq<Wave>, wave_index: nat, k: nat)
    requires
        can_solve_wave(waves, wave_index, k),
    ensures
        wave_index < waves.len(),
        k > 0,
        waves[wave_index as int].monsters > 0
{
}

proof fn valid_waves_properties(waves: Seq<Wave>, i: int)
    requires
        valid_waves(waves),
        0 <= i < waves.len(),
    ensures
        waves[i].start_time <= waves[i].end_time,
        waves[i].monsters > 0,
        (i > 0 ==> waves[i-1].end_time <= waves[i].start_time)
{
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
/* code modified by LLM (iteration 5): Fixed ghost_closure issue and result variable usage */
{
    proof {
        let can_solve = check_can_solve_all_waves(waves@, k as nat);
        if !can_solve {
            return -1;
        }
    }
    
    let mut total_bullets: i32 = 0;
    let mut current_bullets: u32 = k as u32;
    let mut i: usize = 0;
    
    while i < waves.len()
        invariant
            i <= waves.len(),
            total_bullets == calculate_minimum_bullets_helper(waves@, k as nat, i as nat, current_bullets as nat) as i32,
            current_bullets <= k as u32,
            can_solve_all_waves(waves@, k as nat),
    {
        let wave = waves[i].clone();
        
        proof {
            can_solve_wave_implies_valid(waves@, i as nat, k as nat);
        }
        
        if current_bullets >= wave.monsters as u32 {
            total_bullets += wave.monsters as i32;
            current_bullets = (k as u32) - (wave.monsters as u32);
        } else {
            let reloads_needed = calculate_reloads_needed_exec(wave.monsters as u32, k as u32);
            total_bullets += ((reloads_needed + 1) * k as u32) as i32;
            current_bullets = (k as u32) - (wave.monsters as u32 - reloads_needed * k as u32);
        }
        
        i += 1;
    }
    
    total_bullets
}
// </vc-code>


}

fn main() {}