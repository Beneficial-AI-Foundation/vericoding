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
spec fn sum_bullets_upto(waves: Seq<Wave>, k: nat, end_index: nat) -> int
    decreases end_index
{
    if end_index == 0 {
        0
    } else {
        let i = (end_index - 1) as int;
        let prev_sum = sum_bullets_upto(waves, k, end_index - 1);
        let wave = waves[i];
        let bullets_for_this_wave: int = if k >= wave.monsters {
            wave.monsters as int
        } else {
            let num_clips = ((wave.monsters - 1) as int / k as int) + 1;
            num_clips * (k as int)
        };
        prev_sum + bullets_for_this_wave
    }
}

lemma fn lemma_sum_and_helper_relation(waves: Seq<Wave>, k: nat, j: nat)
    requires
        j <= waves.len(),
        k > 0,
        valid_waves(waves),
        can_solve_all_waves(waves, k),
    ensures
        sum_bullets_upto(waves, k, j) + calculate_minimum_bullets_helper(waves, k, j, k) as int
            == calculate_minimum_bullets(waves, k) as int,
    decreases j
{
    if j > 0 {
        lemma_sum_and_helper_relation(waves, k, j - 1);
        let wave = waves[(j - 1) as int];
        let helper_val_j = calculate_minimum_bullets_helper(waves, k, j, k);
        let helper_val_j_minus_1 = calculate_minimum_bullets_helper(waves, k, j-1, k);

        let bullets_for_this_wave: int = if k >= wave.monsters {
            wave.monsters as int
        } else {
            let num_clips = ((wave.monsters - 1) as int / k as int) + 1;
            (num_clips * k as int) as int
        };
        
        assert(helper_val_j_minus_1 as int == bullets_for_this_wave + helper_val_j as int) by {
            let helper_bullets = if k >= wave.monsters {
                wave.monsters
            } else {
                 let reloads_needed = (((wave.monsters - 1) as int / k as int) + 1) as nat;
                 reloads_needed * k
            };
            assert(helper_val_j_minus_1 == helper_bullets + helper_val_j);
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
{
    let k_nat = k as nat;

    let mut i: usize = 0;
    while i < waves.len()
        invariant
            valid_waves(waves@),
            k > 0,
            0 <= i <= waves.len(),
            forall|j: int| 0 <= j < i as int ==> #[trigger] can_solve_wave(waves@, j as nat, k_nat),
    {
        let wave = &waves[i];
        let time_available = wave.end_time - wave.start_time + 1;
        if wave.monsters > time_available * k_nat {
            return -1;
        }

        if i > 0 {
            let prev_wave = &waves[i-1];
            let reloads_needed = calculate_reloads_needed(prev_wave.monsters, k_nat);
            let time_gap = wave.start_time - prev_wave.end_time;
            if reloads_needed > time_gap {
                return -1;
            }
        }

        proof {
            let current_wave_solved = can_solve_wave(waves@, i as nat, k_nat);
            assert(current_wave_solved) by {
                let wave = waves@[i as int];
                let time_ok = wave.monsters <= (wave.end_time - wave.start_time + 1) * k_nat;
                let reach_ok = i == 0 || can_reach_wave_in_time(waves@, i as nat, k_nat);
                assert(time_ok);
                assert(reach_ok);
            }
            assert forall|j: int| 0 <= j < (i + 1) as int implies #[trigger] can_solve_wave(waves@, j as nat, k_nat) by {
                if j < i {
                    assert(can_solve_wave(waves@, j as nat, k_nat));
                } else {
                    assert(can_solve_wave(waves@, i as nat, k_nat));
                }
            }
        }
        i = i + 1;
    }

    assert(can_solve_all_waves(waves@, k_nat));

    let mut total_bullets: i64 = 0;
    let mut j: usize = 0;
    while j < waves.len()
        invariant
            valid_waves(waves@),
            k > 0,
            can_solve_all_waves(waves@, k_nat),
            0 <= j <= waves.len(),
            total_bullets == sum_bullets_upto(waves@, k_nat, j as nat),
            sum_bullets_upto(waves@, k_nat, j as nat) + calculate_minimum_bullets_helper(waves@, k_nat, j as nat, k_nat) as int == calculate_minimum_bullets(waves@, k_nat) as int,
    {
        lemma_sum_and_helper_relation(waves@, k_nat, j as nat);
        
        let wave = &waves[j];
        let bullets_for_this_wave: i64;
        if k_nat >= wave.monsters {
            bullets_for_this_wave = wave.monsters as i64;
        } else {
            let monsters = wave.monsters as i64;
            let k_i64 = k as i64;
            let num_clips = (monsters - 1) / k_i64 + 1;
            bullets_for_this_wave = num_clips * k_i64;
        }

        total_bullets = total_bullets + bullets_for_this_wave;
        j = j + 1;
        
        proof {
            lemma_sum_and_helper_relation(waves@, k_nat, j as nat);
            assert(total_bullets == sum_bullets_upto(waves@, k_nat, j as nat));
        }
    }

    assert(total_bullets as int == calculate_minimum_bullets(waves@, k_nat) as int);
    assert(total_bullets <= i32::MAX as i64) by {
        assert(calculate_minimum_bullets(waves@, k_nat) as int <= i32::MAX);
    }

    total_bullets as i32
}
// </vc-code>


}

fn main() {}