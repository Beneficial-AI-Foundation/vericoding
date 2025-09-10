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
function CalculateMinimumBulletsHelper(waves: seq<Wave>, k: nat, index: nat, bulletsLeft: nat): nat
    requires k > 0
    requires ValidWaves(waves)
    requires index <= |waves|
    requires bulletsLeft > 0 && bulletsLeft <= k
    decreases |waves| - index
{
    if index >= |waves| then
        0
    else
        var wave := waves[index];
        var bulletsNeeded := wave.monsters;
        var timeAvailable := wave.end_time - wave.start_time + 1;
        var maxShots := timeAvailable * k;
        
        if bulletsNeeded > maxShots then
            0  // This case shouldn't happen due to CanSolveAllWaves precondition
        else
            var shotsUsed := if bulletsLeft >= bulletsNeeded then bulletsNeeded else bulletsLeft;
            var remainingBullets := if bulletsLeft >= bulletsNeeded then (bulletsLeft - bulletsNeeded) else 0;
            var reloads := if bulletsLeft >= bulletsNeeded then 0 else 1;
            
            // Verify we have enough time for reloads
            if index > 0 && reloads > 0 then
                var timeGap := wave.start_time - waves[index-1].end_time;
                assert reloads <= timeGap;  // From CanReachWaveInTime predicate
            
            bulletsNeeded + CalculateMinimumBulletsHelper(waves, k, index + 1, if remainingBullets > 0 then remainingBullets else k)
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
    if !CanSolveAllWaves(waves, k) {
        result := -1;
    } else {
        result := CalculateMinimumBullets(waves, k);
    }
}
// </vc-code>

