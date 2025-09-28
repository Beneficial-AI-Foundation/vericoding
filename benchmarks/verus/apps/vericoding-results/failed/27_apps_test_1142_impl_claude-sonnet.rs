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
/* helper modified by LLM (iteration 5): removed nat/int types from exec code */
fn lemma_reloads_calculation(monsters: nat, k: nat)
    requires k > 0
    ensures calculate_reloads_needed(monsters, k) == if monsters <= k { 0 } else { ((monsters - 1) as int / k as int) as nat }
{
}

fn lemma_wave_solvability(waves: Seq<Wave>, i: nat, k: nat)
    requires
        valid_waves(waves),
        i < waves.len(),
        k > 0,
    ensures
        can_solve_wave(waves, i, k) == (
            waves[i as int].monsters <= (waves[i as int].end_time - waves[i as int].start_time + 1) * k &&
            (i == 0 || can_reach_wave_in_time(waves, i, k))
        )
{
}

fn lemma_bullets_calculation_base(waves: Seq<Wave>, k: nat)
    requires
        waves.len() == 0,
        k > 0,
    ensures calculate_minimum_bullets(waves, k) == 0
{
}

fn nat_to_i32(n: nat) -> (result: i32)
    requires n <= 0x7fff_ffff
    ensures result == n as int
{
    n as i32
}

fn div_ceil(a: u32, b: u32) -> (result: u32)
    requires b > 0
    ensures result as int == ((a - 1) as int / b as int) + 1
{
    (a - 1) / b + 1
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
    /* code modified by LLM (iteration 5): use u32 types instead of nat/int in exec code */
    let mut total_bullets = 0i32;
    let mut current_bullets = k as u32;
    
    let mut i = 0;
    while i < waves.len()
        invariant
            0 <= i <= waves.len(),
            valid_waves(waves@),
            k > 0,
            current_bullets <= k as u32,
    {
        let wave = &waves[i];
        
        // Check if wave can be solved within time constraints
        let time_available = wave.end_time - wave.start_time + 1;
        let max_possible_shots = time_available * (k as nat);
        if wave.monsters > max_possible_shots {
            return -1;
        }
        
        // Check if we can reach this wave in time (for waves after the first)
        if i > 0 {
            let prev_wave = &waves[i - 1];
            let time_gap = wave.start_time - prev_wave.end_time;
            let reloads_needed = if prev_wave.monsters <= k as nat {
                0
            } else {
                ((prev_wave.monsters - 1) as int / k as int) as nat
            };
            if reloads_needed > time_gap {
                return -1;
            }
        }
        
        // Calculate bullets needed for this wave
        let monsters_u32 = wave.monsters as u32;
        if current_bullets >= monsters_u32 {
            total_bullets += monsters_u32 as i32;
            current_bullets -= monsters_u32;
        } else {
            let reloads_needed = div_ceil(monsters_u32, k as u32);
            let bullets_used = reloads_needed * (k as u32);
            total_bullets += bullets_used as i32;
            current_bullets = k as u32;
        }
        
        i += 1;
    }
    
    total_bullets
}
// </vc-code>


}

fn main() {}