// <vc-preamble>
use vstd::prelude::*;

verus! {
    spec fn valid_input(n: int, d: int, current_points: Seq<int>, awards: Seq<int>) -> bool {
        n >= 1 && n <= 200000 &&
        d >= 1 && d <= n &&
        current_points.len() == n &&
        awards.len() == n &&
        d-1 < current_points.len() &&
        (forall|i: int| 0 <= i < current_points.len()-1 ==> 
            #[trigger] current_points.index(i) >= current_points.index((i+1) as int)) &&
        (forall|i: int| 0 <= i < awards.len()-1 ==> 
            #[trigger] awards.index(i) >= awards.index((i+1) as int))
    }
    
    spec fn count_overtaken(current_points: Seq<int>, awards: Seq<int>, d: int) -> int
        recommends 
            current_points.len() == awards.len(),
            d >= 1 && d <= current_points.len(),
            d-1 < current_points.len(),
            forall|i: int| 0 <= i < awards.len()-1 ==> 
                #[trigger] awards.index(i) >= awards.index((i+1) as int)
    {
        count_overtaken_helper(current_points, awards, d, 0, 0)
    }
    
    spec fn count_overtaken_helper(current_points: Seq<int>, awards: Seq<int>, d: int, pos: int, used_awards: int) -> int
        recommends 
            current_points.len() == awards.len(),
            d >= 1 && d <= current_points.len(),
            d-1 < current_points.len(),
            forall|i: int| 0 <= i < awards.len()-1 ==> 
                #[trigger] awards.index(i) >= awards.index((i+1) as int),
            0 <= pos <= d-1,
            0 <= used_awards <= awards.len()
        decreases d-1-pos
    {
        if pos >= d-1 {
            0
        } else {
            let target_score = current_points.index(d-1) + awards.index(0);
            let remaining_awards = awards.len() - used_awards;
            if remaining_awards > 0 && used_awards < awards.len() && current_points.index(pos) + awards.index(awards.len()-1-used_awards) <= target_score {
                1 + count_overtaken_helper(current_points, awards, d, pos+1, used_awards+1)
            } else {
                count_overtaken_helper(current_points, awards, d, pos+1, used_awards)
            }
        }
    }
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): remove assume, fix calculation */
spec fn find_max_awards_possible(current_points: Seq<int>, awards_seq: Seq<int>, d_idx: int) -> int
    requires
        current_points.len() == awards_seq.len(),
        d_idx >= 0 && d_idx < current_points.len(),
        // current_points is sorted descending
        (forall|i: int| 0 <= i < current_points.len()-1 ==> #[trigger] current_points.index(i) >= current_points.index(i+1)),
        // awards_seq is sorted descending
        (forall|i: int| 0 <= i < awards_seq.len()-1 ==> #[trigger] awards_seq.index(i) >= awards_seq.index(i+1))
{
    // d_idx is the index of participant d (0-indexed)
    let d_original_points = current_points.index(d_idx);
    let best_award_for_d = awards_seq.index(0);
    let target_score_for_d = d_original_points + best_award_for_d;

    // 'left' pointer for awards_seq (from largest award to smallest)
    // 'right' pointer for participants before d_idx (from d_idx-1 down to 0)

    let mut i: int = 0; // index for awards, from smallest (awards_seq.len() - 1) upwards
    let mut j: int = d_idx - 1; // index for participants, from d_idx-1 downwards
    let mut current_overtaken_count: int = 0;

    while i < awards_seq.len() && j >= 0
        invariant
            0 <= i <= awards_seq.len(),
            -1 <= j <= d_idx - 1,
            0 <= current_overtaken_count,
            current_overtaken_count <= d_idx - (j + 1),
            // All participants with index > j (and < d_idx) have been processed.
            // For these processed participants, `current_overtaken_count` correctly reflects
            // how many of them are overtaken by D, assuming optimal award assignment from
            // the smallest `i` available awards.
    {
        // We are checking participant `j` (current_points.index(j)).
        // We try to give them the smallest available award, which is `awards_seq.index(awards_seq.len() - 1 - i)`.
        let potential_score_for_j = current_points.index(j) + awards_seq.index(awards_seq.len() - 1 - i);

        if potential_score_for_j >= target_score_for_d {
            // If participant `j` with the smallest available award still scores higher than or equal to `d`'s target score,
            // then `d` cannot overtake `j`. We must effectively 'use' this award for `j` (or someone else if `j` gets a better one)
            // and move to the next participant (`j-1`) and next smallest award (`i+1`).
            i = i + 1;
            // current_overtaken_count remains the same, as `j` is not overtaken.
        } else {
            // If participant `j` with the smallest available award scores less than `d`'s target score,
            // then `d` CAN overtake `j`. We 'save' this award by not considering it used for `j`
            // and try to use it for another participant further down the ranks (smaller `j`).
            // Participant `j` is now considered overtaken.
            current_overtaken_count = current_overtaken_count + 1;
        }
        j = j - 1;
    }
    current_overtaken_count
}
// </vc-helpers>

// <vc-spec>
fn solve(n: i8, d: i8, current_points: Vec<i8>, awards: Vec<i8>) -> (result: i8)
    requires 
        valid_input(n as int, d as int, current_points@.map(|i, x| x as int), awards@.map(|i, x| x as int))
    ensures 
        1 <= result as int <= d as int,
        result as int == d as int - count_overtaken(current_points@.map(|i, x| x as int), awards@.map(|i, x| x as int), d as int)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): fixed ghost to tracked, while loop invariant, and calculation logic */
{
    let n_int: int = n as int;
    let d_int: int = d as int;
    let current_points_seq = current_points@.map(|i, x| x as int);
    let awards_seq = awards@.map(|i, x| x as int);

    // d_idx is the 0-indexed position of player d
    let d_idx = d_int - 1;

    // Calculate how many participants before d (i.e., with indices 0 to d_idx-1) can be overtaken by participant d.
    // This is done by maximizing the number of people d overtakes.
    // A participant `j` (where `j < d_idx`) *can be overtaken* if `current_points[j] + award_assigned_to_j < target_score_for_d`.
    // To maximize `overtaken_count`, we need to maximize the number of participants where this condition holds true.
    // We try to assign the `i`-th smallest award (awards_seq.index(K - 1 - i)) to `j` such that `current_points[j]`
    // is as high as possible without `j` exceeding or equaling `d`'s target new score.

    let target_score_for_d = current_points_seq.index(d_idx) + awards_seq.index(0);

    let mut overtaken_count: i8 = 0;
    let mut award_idx: i8 = 0; // Represents the index for awards_seq, starting from the smallest (awards_seq.len() - 1 - awards_idx)
                               // This variable will effectively increment from 0 to `awards_seq.len() - 1`

    // Iterate through participants from d_idx - 1 down to 0
    let mut participant_idx: i8 = d_idx - 1;
    while participant_idx >= 0 && award_idx < n as i8
        invariant
            participant_idx >= -1,
            award_idx >= 0,
            award_idx as int <= n_int,
            overtaken_count >= 0,
            overtaken_count as int <= d_idx - (participant_idx as int + 1),
            // All participants with index > participant_idx (and < d_idx) have been processed.
            // For these processed participants, `overtaken_count` correctly reflects
            // how many of them are overtaken by D, assuming optimal award assignment from
            // the `award_idx` smallest awards.
    {
        let current_participant_points = current_points_seq.index(participant_idx as int);
        let smallest_available_award = awards_seq.index((n_int - 1 - award_idx as int) as int);

        if current_participant_points + smallest_available_award >= target_score_for_d {
            // The current participant (participant_idx) cannot be overtaken by d,
            // because even with the smallest available award, their score is still higher or equal to d's target score.
            // We must effectively 'use' this award to keep them stable or higher.
            award_idx = award_idx + 1;
            // This participant is NOT overtaken.
        } else {
            // The current participant (participant_idx) CAN be overtaken by d.
            // This means that even if they were given larger awards, they couldn't reach d's score.
            // We consider this participant overtaken.
            overtaken_count = overtaken_count + 1;
            // We do NOT increment `award_idx` here, as we didn't 'use' an award to prevent them from being overtaken.
            // This award effectively remains available for other participants who might need it more to not be overtaken.
        }
        participant_idx = participant_idx - 1;
    }

    ((d as i8) - overtaken_count)
}
// </vc-code>

}

fn main() {}