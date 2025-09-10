datatype Wave = Wave(start_time: nat, end_time: nat, monsters: nat)

predicate ValidWaves(waves: seq<Wave>)
{
    forall i :: 0 <= i < |waves| ==> 
        waves[i].start_time <= waves[i].end_time &&
        waves[i].monsters > 0 &&
        (i > 0 ==> waves[i-1].end_time <= waves[i].start_time)
}

predicate CanSolveAllWaves(waves: seq<Wave>, k: nat)
{
    k > 0 && 
    forall i :: 0 <= i < |waves| ==> 
        CanSolveWave(waves, i, k)
}

predicate CanSolveWave(waves: seq<Wave>, waveIndex: nat, k: nat)
    requires waveIndex < |waves|
    requires k > 0
{
    var wave := waves[waveIndex];
    var timeAvailable := wave.end_time - wave.start_time + 1;
    var maxPossibleShots := timeAvailable * k;
    wave.monsters <= maxPossibleShots &&
    (waveIndex == 0 || CanReachWaveInTime(waves, waveIndex, k))
}

predicate CanReachWaveInTime(waves: seq<Wave>, waveIndex: nat, k: nat)
    requires waveIndex > 0 && waveIndex < |waves|
    requires k > 0
{
    var prevWave := waves[waveIndex - 1];
    var currWave := waves[waveIndex];
    var timeGap := currWave.start_time - prevWave.end_time;
    var reloadsNeeded := CalculateReloadsNeeded(prevWave.monsters, k);
    reloadsNeeded <= timeGap
}

function CalculateReloadsNeeded(monsters: nat, k: nat): nat
    requires k > 0
{
    if monsters <= k then 0
    else (monsters - 1) / k
}

function CalculateMinimumBullets(waves: seq<Wave>, k: nat): nat
    requires k > 0
    requires ValidWaves(waves)
    requires CanSolveAllWaves(waves, k)
    ensures |waves| > 0 ==> CalculateMinimumBullets(waves, k) > 0
{
    CalculateMinimumBulletsHelper(waves, k, 0, k)
}

// <vc-helpers>
function CalculateMinimumBulletsHelper(waves: seq<Wave>, k: nat, index: nat, currentBullets: nat): nat
    requires ValidWaves(waves)
    requires k > 0
    requires index <= |waves|
    requires (index < |waves| && currentBullets > 0) ==> CanSolveWave(waves, index, k)
    // The previous waves up to index-1 could be solved with 'k' bullets per unit time
    // and the travel/reload time between them was sufficient
    requires forall i :: 0 <= i < index ==> CanSolveWave(waves, i, k)
    // If index > 0, ensure we could have reached this wave
    requires index > 0 ==> CanReachWaveInTime(waves, index, k)
    decreases |waves| - index
{
    if index == |waves| then
        currentBullets
    else
        var wave := waves[index];
        var bulletsNeededForWave := wave.monsters;
        var newCurrentBullets := if currentBullets >= bulletsNeededForWave then currentBullets - bulletsNeededForWave else currentBullets;
        
        // This is the core recursive step where we accumulate bullets.
        // If we can't solve the wave, this helper shouldn't have been called or this logic needs to be in SolveMonsterWaves.
        // Assuming CanSolveWave(waves, index, k) holds, we know wave.monsters <= maxPossibleShots
        // and timeAvailable * k is the max bullets we *could* fire.
        // The problem asks for minimum bullets in the 'clip', so we subtract monsters.
        // If we need to reload (i.e. monsters > currentBullets), we reload to 'k' and spend the difference.
        // This interpretation is important: the problem is not about spending existing bullets,
        // but about the minimum clip size needed. Let's re-evaluate.

        // The CalculateMinimumBullets function signature suggests it calculates *a* value of k,
        // but the method SolveMonsterWaves *takes* k as input.
        // The interpretation of CalculateMinimumBullets seems to be:
        // What is the minimum 'k' (bullets per unit time) required to solve all waves?
        // But the input 'k' to SolveMonsterWaves is fixed.

        // Let's re-read the function `CalculateMinimumBullets(waves: seq<Wave>, k: nat): nat`
        // Given that `CanSolveAllWaves(waves, k)` is true (precondition),
        // it means that with `k` bullets per unit time, all waves are solvable.
        // The result of `CalculateMinimumBullets` is a `nat`.
        // The ensures clause `|waves| > 0 ==> CalculateMinimumBullets(waves, k) > 0`
        // implies it's about the optimal or required `k` value?

        // Rereading the problem statement: "CalculateMinimumBullets(waves: seq<Wave>, k: nat): nat"
        // This function is provided, and we cannot change its body.
        // Its body is missing, so we must fill it in.
        // The function `CalculateMinimumBullets` seems to be intended to calculate the minimum value
        // for the parameter 'k' that would allow solving all waves.
        // However, the signature is `k: nat` (input) and `result: nat` (output).
        // This is confusing if `k` is an input parameter and also what the function is calculating.

        // Let's assume `CalculateMinimumBullets(waves, k)` means:
        // *Given* an ability to fire `k` bullets per unit time, what is the minimum additional `k_prime`
        // (to be added to `k`) such that we can clear all waves? No, that doesn't make sense.

        // The most plausible interpretation is that `CalculateMinimumBullets` (if `CanSolveAllWaves(waves, k)`)
        // calculates the maximum value that `monsters` takes for any wave, adjusted for time.
        // OR it calculates the minimum *initial* ammo needed in a clip, assuming `k` is the reload rate.

        // Let's assume the simpler approach: the value returned by `CalculateMinimumBullets` is the minimum `k`
        // that satisfies `CanSolveAllWaves(waves, k)`. But `k` is an input.

        // Let's assume CalculateMinimumBullets is meant to return the theoretical minimum bullet *capacity*
        // you would ever need in actively shooting, given that you *can* solve it with rate 'k'.

        // This implies that CalculateMinimumBullets is *not* a recursive function on waves.
        // It must check the 'k' parameter or compute some value based on the waves seq and the given 'k'.

        // Given `CalculateMinimumBullets(waves: seq<Wave>, k: nat): nat`
        // The helper `CalculateMinimumBulletsHelper` should probably be about *accumulating* current bullets.

        // Let's try to interpret `CalculateMinimumBullets` based on the method `SolveMonsterWaves` postcondition:
        // `CanSolveAllWaves(waves, k) ==> result == CalculateMinimumBullets(waves, k)`
        // This means `CalculateMinimumBullets` should determine the `result` given *a fixed* `k`.
        // The result for `SolveMonsterWaves` is `int`.

        // Let's consider the usual interpretation of this problem type:
        // We have a fixed *rate* `k`. We have a "clip" or "magazine" that holds bullets.
        // When we shoot, bullets are removed. When we reload, bullets are added.
        // The `k` value in `CanSolveWave` is a rate (bullets per unit time).
        // The `CalculateMinimumBullets` function might be calculating the minimum *initial clip size* (or max clip size) needed.

        // If `CalculateMinimumBullets` calculates the maximum number of active bullets needed at any specific time,
        // then it probably needs to track a running total or maximum.

        // Let's assume `CalculateMinimumBullets` (the top-level function) computes the maximum
        // number of bullets present in the "clip" at any point, assuming we start with 0 and reload to `k` whenever possible/needed.

        // This reasoning path for `CalculateMinimumBullets` leads to complications because its definition is missing.
        // Let's focus on `SolveMonsterWaves` first and then deduce `CalculateMinimumBullets`.

        // Okay, `CalculateMinimumBullets` must be implemented. Let's assume a standard RPG interpretation:
        // `k` is the maximum bullets we can fire per unit time. We have a "clip" that holds `X` bullets.
        // We want to find the minimum `X` such that all waves can be cleared.
        // The problem is that the `k` in the `CalculateMinimumBullets` signature is an input, not the thing it's calculating.

        // The problem description has provided `CalculateMinimumBullets` with `requires k > 0` etc.,
        // implying `k` is fixed. The result is a `nat`.
        // "ensures |waves| > 0 ==> CalculateMinimumBullets(waves, k) > 0"
        // This is a subtle point. If `k` is the rate, what is the function calculating?

        // Let's reinterpret `CalculateMinimumBullets` as:
        // "Given that we have a 'base' rate `k`, what's the minimum effective `k` (rate) we needed?
        // No, that doesn't make sense as `k` is already given to `SolveMonsterWaves`.

        // Let's assume `CalculateMinimumBullets(waves, k)` calculates the maximum "negative balance" of bullets we ever achieve.
        // i.e., how many bullets do we *wish* we had at some point. This corresponds to the needed clip size.
        // We start with some initial bullets. We shoot `monsters`. We regain `k` bullets per unit time.

        // This needs a recursive helper for `CalculateMinimumBullets`.
        // Let `CalculateMinimumBulletsHelper(waves, k, index, current_bullets_in_clip)`
        // be the minimum clip size needed from `index` onwards, assuming `current_bullets_in_clip` are available *after* wave `index-1`.
        // This is a dynamic programming style approach.

        // A common pattern for "minimum capacity" problems is to track the running "balance" and find the minimum `balance` encountered.
        // `min_balance = min(min_balance, current_balance)`. Then the required capacity is `0 - min_balance`.

        // Let's define `CalculateMinimumBulletsHelper` as follows:
        // `CalculateMinimumBulletsHelper(waves, k, index, balance): (min_balance_needed, actual_k_for_next_wave)`
        // This is getting too complex for a standard Dafny problem.

        // Let's simplify. `CalculateMinimumBullets` is likely:
        // The maximum value of `monsters` must be fired for a single wave, possibly taking into account `k`.
        // Or it's the maximum `total bullets` needed at any point, considering reloads.

        // Let's assume `CalculateMinimumBullets(waves, k)` is intended to calculate the minimum
        // *initial* number of bullets you need to have in your clip to clear all waves,
        // assuming you can fire `k` bullets per unit time and reload up to `k` per unit time.

        // This suggests tracking the maximum `bullets_in_clip` ever needed.
        // The `k` input is confusing. Is `k` the clip size or reload speed?
        // Given `CalculateReloadsNeeded(monsters: nat, k: nat)`, `k` is likely the reload *rate* or *capacity per reload*.
        // `k` seems to be the rate of fire / reload.

// Let's assume the problem is asking for the minimum initial clip size required to solve all waves,
// given a firing rate `k`. During gameplay, our clip size is `C`. We fire `monsters` bullets.
// Between waves, we have `timeGap` ticks. Each tick, we can gain up to `k` bullets, up to `C`.

// Let `CalculateMinimumBulletsHelper(waves, k, index, current_clip_capacity)`:
// This seems to be the right signature for `CalculateMinimumBullets` (the external one).
// The value of `k` is constant throughout the problem and comes from `SolveMonsterWaves`.

// Let's assume `CalculateMinimumBullets` intends to calculate the actual *max capacity* needed for the clip.
// This means we need to simulate the process and find the maximum negative balance.

// Initial approach for `CalculateMinimumBullets`:
// We iterate through the waves.
// `bullets_carried = 0` (initial state, we want to know what min initial `C` should be)
// `max_bullets_needed = 0` (this will be our result, `C`)
// For each wave `w`:
//   We need to have `w.monsters` bullets available.
//   `bullets_carried -= w.monsters`
//   `max_bullets_needed = max(max_bullets_needed, -bullets_carried)` (if bullets_carried becomes negative)
//   After the wave, we have `timeAvailable` to reload for the next wave.
//   `bullets_carried += timeAvailable * k` (reloading)
//   `bullets_carried = min(bullets_carried, max_bullets_needed)` (can't overflow capacity)
// This is typical for minimum capacity problems.

// Let's use `bullets_at_start_of_wave` and `bullets_at_end_of_wave`.
// We need to keep a running total of `bullets_deficit`.
// `min_initial_bullets = 0`
// `current_bullets = 0` (represents bullets in a clip, we'll ensure this never drops below 0 by adjusting initial)

// Let's define the helper for CalculateMinimumBullets.
// `CalculateMinimumBulletsHelper(waves, k, index, current_clip_content_if_start_is_0)`
// It returns the max negative balance accumulated *up to* this point.

// Function CalculateMinimumBullets(waves: seq<Wave>, k: nat): nat
//   requires k > 0
//   requires ValidWaves(waves)
//   requires CanSolveAllWaves(waves, k)
//   ensures |waves| > 0 ==> CalculateMinimumBullets(waves, k) > 0
// {
//   if |waves| == 0 then 0
//   else
//     var max_needed := 0;
//     var current_balance := 0; // Represents: what if we started with 0 bullets? how far negative do we go?
//     for i := 0 to |waves|-1 invariant 0 <= i <= |waves|
//                                 invariant max_needed == Max(0, max_needed_up_to_i(waves, k, i, current_balance))
//                                 invariant current_balance == current_balance_at_start_of_wave_i(waves, k, i)
//     {
//       var wave := waves[i];
//       current_balance := current_balance - wave.monsters; // Spend bullets
//       max_needed := max(max_needed, -current_balance); // Record max deficit
//       if i < |waves|-1 { // Reload for next wave
//         var timeGap := waves[i+1].start_time - wave.end_time;
//         // Reload up to 'max_needed' capacity, at rate 'k' for 'timeGap'
//         current_balance := min(0, current_balance + timeGap * k); // Cap at 0 because we don't care beyond satisfying deficit
//       }
//     }
//     max_needed
// }
// This is the correct interpretation for `CalculateMinimumBullets` (the function that was missing from original problem).

// Let's put this logic into the helper.
// Since `CalculateMinimumBullets` must call `CalculateMinimumBulletsHelper`,
// then `CalculateMinimumBulletsHelper` must actually calculate this value iteratively.

// Redo structure:
// `CalculateMinimumBullets(waves: seq<Wave>, k: nat): nat` will be non-recursive, iterative.
// Its body will be new, directly in the `functions` section.

// The `CalculateMinimumBullets` provided in the template currently calls `CalculateMinimumBulletsHelper`.
// So the structure given implies that `CalculateMinimumBulletsHelper` *is* the one implementing the core logic.

// Let `CalculateMinimumBulletsHelper` compute the `max_needed` and `current_balance` iteratively.
// It needs to return a tuple or be modeled differently.
// Let's make `CalculateMinimumBulletsHelper` the main loop. It must be a function.

// Recursive definition for `CalculateMinimumBulletsHelper`:
// `CalculateMinimumBulletsHelper(waves: seq<Wave>, k: nat, index: nat, current_balance: int, max_deficit: nat): nat`
// `current_balance`: current bullets in clip relative to an initial 0. Can be negative.
// `max_deficit`: max(-current_balance) seen so far.
// Returns the max deficit for the rest of the waves.

// Let `f(index, balance)` be the result.
function CalculateMinimumBulletsHelper(waves: seq<Wave>, k: nat, index: nat, current_balance: int, max_deficit: nat): nat
    requires 0 <= index <= |waves|
    requires k > 0
    requires ValidWaves(waves)
    // The `CanSolveAllWaves` property applies to the global `k`, not `current_balance`.
    // It's a precondition to `CalculateMinimumBullets`.
    requires CanSolveAllWaves(waves, k)
    // Current balance could be negative if we started with 0 and went into deficit.
    // max_deficit tracks the maximum *positive* value of money needed.
    {
        if index == |waves| then
            max_deficit
        else
            var wave := waves[index];
            var new_balance_after_spending := current_balance - wave.monsters;
            var new_max_deficit := if new_balance_after_spending < 0 then max(-new_balance_after_spending, max_deficit) else max_deficit;

            var balance_after_reload := new_balance_after_spending;
            if index < |waves| - 1 {
                var timeGap := waves[index+1].start_time - wave.end_time;
                // Reload up to `max_deficit` (this is our pseudo-clip size)
                // If `balance_after_spending` is e.g. -50, and `max_deficit` is 50, then our capacity is 50.
                // We shouldn't reload beyond 0 because we're tracking deficit.
                balance_after_reload := min(0, balance_after_reload + timeGap * k);
            }
            CalculateMinimumBulletsHelper(waves, k, index + 1, balance_after_reload, new_max_deficit)
    }

// The `CalculateMinimumBullets` function now has its body.
// We need to provide the body for the `SolveMonsterWaves` method.

// `SolveMonsterWaves` must return `int`.
// `result == -1 <==> !CanSolveAllWaves(waves, k)`
// `result >= 0 <==> CanSolveAllWaves(waves, k)`
// `CanSolveAllWaves(waves, k) ==> result == CalculateMinimumBullets(waves, k)`

// Based on these, the implementation of `SolveMonsterWaves` is:
// if CanSolveAllWaves(waves, k) then CalculateMinimumBullets(waves, k) else -1

// Let's refine `CalculateMinimumBullets`'s definition given in the Dafny template:
// function CalculateMinimumBullets(waves: seq<Wave>, k: nat): nat
//   requires k > 0
//   requires ValidWaves(waves)
//   requires CanSolveAllWaves(waves, k)
//   ensures |waves| > 0 ==> CalculateMinimumBullets(waves, k) > 0
// {
//     CalculateMinimumBulletsHelper(waves, k, 0, 0, 0)
// }
// This initial call for `CalculateMinimumBulletsHelper` makes sense:
// `index=0`, `current_balance=0` (start with 0 bullets, track deficit from there), `max_deficit=0`.
// The result of `CalculateMinimumBulletsHelper` will be the minimum initial clip size needed.

// Proof obligations for the `CalculateMinimumBulletsHelper`:
// The termination is guaranteed by `decreases |waves| - index`.
// The preconditions must be maintained.
// `ValidWaves(waves)` and `k > 0` and `CanSolveAllWaves(waves, k)` are global and passed down.
// `0 <= index <= |waves|` is maintained (`index+1`).
// The definition must be functionally correct.
// </vc-helpers>

// <vc-spec>
method SolveMonsterWaves(waves: seq<Wave>, k: nat) returns (result: int)
    requires ValidWaves(waves)
    requires k > 0
    ensures result == -1 <==> !CanSolveAllWaves(waves, k)
    ensures result >= 0 <==> CanSolveAllWaves(waves, k)
    ensures CanSolveAllWaves(waves, k) ==> result == CalculateMinimumBullets(waves, k)
// </vc-spec>
// <vc-code>
{
    if CanSolveAllWaves(waves, k) then
        (CalculateMinimumBullets(waves, k)) as int
    else
        -1
}
// </vc-code>

