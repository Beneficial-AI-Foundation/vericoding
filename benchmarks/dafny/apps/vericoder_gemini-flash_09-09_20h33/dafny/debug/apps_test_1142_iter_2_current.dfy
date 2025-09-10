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
    requires index <= |waves| // Changed this to accommodate the base case where index == |waves|
    requires CanSolveAllWaves(waves, k)
    // Add additional lemma (or property) related to `ValidWaves` which can be used to prove properties like:
    // When `index` < `|waves|`, `waves[index]` is a valid `Wave`.
{
    if index == |waves| then
        0
    else
        var wave := waves[index];
        var bullets_for_this_wave := wave.monsters;
        var new_bullets := current_bullets;

        // If it's not the first wave, consider the time gap
        if index > 0 && ValidWaves(waves) {
            var prev_wave := waves[index-1];
            var time_gap := wave.start_time - prev_wave.end_time;
            
            // Reload bullets during the time gap
            new_bullets := new_bullets + time_gap * k;
        }

        // If current bullets are not enough, need to buy more
        if new_bullets < bullets_for_this_wave then
            var bullets_to_buy := bullets_for_this_wave - new_bullets;
            bullets_to_buy + CalculateMinimumBulletsHelper(waves, k, index + 1, k)
        else
            CalculateMinimumBulletsHelper(waves, k, index + 1, new_bullets - bullets_for_this_wave + k)
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
        return CalculateMinimumBulletsHelper(waves, k, 0, k);
}
// </vc-code>

