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
function method CalculateMinimumBulletsHelper(waves: seq<Wave>, k: nat, index: nat, bullets_remaining: nat): nat
    requires 0 <= index <= |waves|
    requires k > 0
    requires ValidWaves(waves)
    requires CanSolveAllWaves(waves, k)
    requires |waves| > 0 ==> bullets_remaining > 0
    decreases |waves| - index
{
    if index == |waves| then 0
    else
        var wave := waves[index];
        var bullets_consumed_this_round: nat := wave.monsters;
        var bullets_needed_next_round: nat := if (index+1 < |waves|) then bullets_remaining else k;
        var bullets_needed_for_reload: nat := if (bullets_consumed_this_round > bullets_remaining) then
            CalculateReloadsNeeded(bullets_consumed_this_round, bullets_remaining)
        else 0;

        if (index+1 < |waves|) then
            var time_gap := waves[index+1].start_time - wave.end_time;
            var reloads_possible_in_gap := time_gap * bullets_needed_next_round;
            
            // Bullets carried over to next round
            var carried_bullets := if bullets_consumed_this_round <= bullets_remaining then
                bullets_remaining - bullets_consumed_this_round
            else
                bullets_needed_next_round - (reloads_possible_in_gap - bullets_needed_for_reload);
                
            bullets_consumed_this_round + CalculateMinimumBulletsHelper(waves, k, index+1, if carried_bullets <= 0 then bullets_needed_next_round else carried_bullets)
        else
            bullets_consumed_this_round
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
        -1
    else
        CalculateMinimumBulletsHelper(waves, k, 0, k)
}
// </vc-code>

