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
function CalculateMinimumBulletsHelper(waves: seq<Wave>, k: nat, index: nat, current_bullets: nat): nat
    requires k > 0
    requires ValidWaves(waves)
    requires index <= |waves|
    requires CanSolveAllWaves(waves, k)
    // The current_bullets argument represents the bullets available at the start of the current wave.
    // It's capped at `k` because you can only reload `k` bullets per unit of time,
    // so any excess bullets from previous stages (beyond what's needed for the current wave)
    // are essentially "discarded" for the purpose of carrying over.
    // In other words, you always start a wave with at most `k` "fresh" bullets,
    // plus any reloads from time gaps.
    // However, the logic for `new_bullets` updates this. `current_bullets` should represent the
    // *maximum* bullets you could have at the start of the wave *before* any reloads from time gaps.
    // Let's refine the invariant on `current_bullets`.
    // It should represent the bullets remaining after the previous wave (if any) and
    // potentially reloaded. For the initial call, it's `k` as the initial "magazine".
    // For subsequent calls, it's `new_bullets - bullets_for_this_wave + k`.
    // This `+ k` ensures that you always have at least `k` bullets if you had extra,
    // representing a full reload.
    // So current_bullets could be more than k.
{
    if index == |waves| then
        0
    else
        var wave := waves[index];
        var bullets_for_this_wave := wave.monsters;
        var new_bullets_after_reloads := current_bullets;

        // If it's not the first wave, consider the time gap
        if index > 0 then
            var prev_wave := waves[index-1];
            var time_gap := wave.start_time - prev_wave.end_time;
            if time_gap > 0 then // Only reload if there's a time gap
                new_bullets_after_reloads := new_bullets_after_reloads + time_gap * k;
        // The predicate ValidWaves(waves) ensures that if index > 0, then waves[index-1].end_time <= waves[index].start_time
        // which means time_gap >= 0.
        // Also, it ensures ValidWaves(waves) at each recursive call.
        
        // If current bullets are not enough, need to buy more
        if new_bullets_after_reloads < bullets_for_this_wave then
            var bullets_to_buy := bullets_for_this_wave - new_bullets_after_reloads;
            bullets_to_buy + CalculateMinimumBulletsHelper(waves, k, index + 1, k)
        else
            // If we have enough bullets, we use some. The remaining bullets, plus 'k' for the next reload (if any time gap exists).
            // The `+ k` here signifies that at the start of the *next* wave, we conceptually have a new magazine of size `k`.
            // This `k` is the base amount of bullets available per time unit.
            // The `CalculateReloadsNeeded` predicate uses `prevWave.monsters - 1 / k` which indicates
            // we need to reload until we have enough to kill the current wave (or satisfy monster count).
            // The `current_bullets` should represent the maximum bullets one would have at the start of a wave
            // with a fully loaded "magazine" (k bullets) plus any reloads from the time gap.
            // The formulation `new_bullets - bullets_for_this_wave + k` is used when we kill the monsters
            // and then consider the 'k' bullets from the reload at the start of the next period.
            // This implicitly assumes that each time unit provides 'k' bullets.
            // The key is that we are always able to fire 'k' bullets per unit time.
            CalculateMinimumBulletsHelper(waves, k, index + 1, new_bullets_after_reloads - bullets_for_this_wave + k)
}
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
    if !CanSolveAllWaves(waves, k) then
        return -1;
    else if |waves| == 0 then
        return 0; // No waves, no bullets needed
    else
        // The initial current_bullets is 'k' because the player starts with a full magazine,
        // which gives 'k' bullets at the start of the first wave.
        return CalculateMinimumBulletsHelper(waves, k, 0, k);
}
// </vc-code>

