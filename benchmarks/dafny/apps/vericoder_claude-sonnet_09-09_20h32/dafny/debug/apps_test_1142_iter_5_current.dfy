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
function CalculateMinimumBulletsHelper(waves: seq<Wave>, k: nat, waveIndex: nat, currentBullets: nat): nat
    requires k > 0
    requires ValidWaves(waves)
    requires 0 <= waveIndex <= |waves|
    requires currentBullets >= 0
    ensures waveIndex < |waves| ==> CalculateMinimumBulletsHelper(waves, k, waveIndex, currentBullets) > 0
    ensures waveIndex >= |waves| ==> CalculateMinimumBulletsHelper(waves, k, waveIndex, currentBullets) == currentBullets
    decreases |waves| - waveIndex
{
    if waveIndex >= |waves| then
        currentBullets
    else
        var wave := waves[waveIndex];
        var bulletsNeeded := wave.monsters;
        var bulletsToUse := if currentBullets >= bulletsNeeded then bulletsNeeded else currentBullets;
        var remainingMonsters := bulletsNeeded - bulletsToUse;
        var additionalBullets := remainingMonsters;
        var bulletsAfterWave := currentBullets - bulletsToUse + additionalBullets;
        
        if waveIndex + 1 < |waves| then
            var timeGap := waves[waveIndex + 1].start_time - wave.end_time;
            var reloadsNeeded := CalculateReloadsNeeded(wave.monsters, k);
            var bulletsAfterReload := if reloadsNeeded <= timeGap then k else bulletsAfterWave;
            var nextBullets := if bulletsAfterReload == 0 && waveIndex + 1 < |waves| then 1 else bulletsAfterReload;
            CalculateMinimumBulletsHelper(waves, k, waveIndex + 1, nextBullets)
        else
            var nextBullets := if bulletsAfterWave == 0 then 1 else bulletsAfterWave;
            CalculateMinimumBulletsHelper(waves, k, waveIndex + 1, nextBullets)
}

method CheckCanSolveAllWaves(waves: seq<Wave>, k: nat) returns (canSolve: bool)
    requires ValidWaves(waves)
    requires k > 0
    ensures canSolve == CanSolveAllWaves(waves, k)
{
    if |waves| == 0 {
        return true;
    }
    
    var i := 0;
    while i < |waves|
        invariant 0 <= i <= |waves|
        invariant forall j :: 0 <= j < i ==> CanSolveWave(waves, j, k)
    {
        var wave := waves[i];
        var timeAvailable := wave.end_time - wave.start_time + 1;
        var maxPossibleShots := timeAvailable * k;
        
        if wave.monsters > maxPossibleShots {
            assert !CanSolveWave(waves, i, k);
            assert !CanSolveAllWaves(waves, k);
            return false;
        }
        
        if i > 0 {
            var prevWave := waves[i - 1];
            var timeGap := wave.start_time - prevWave.end_time;
            var reloadsNeeded := CalculateReloadsNeeded(prevWave.monsters, k);
            if reloadsNeeded > timeGap {
                assert !CanReachWaveInTime(waves, i, k);
                assert !CanSolveWave(waves, i, k);
                assert !CanSolveAllWaves(waves, k);
                return false;
            }
        }
        
        i := i + 1;
    }
    
    return true;
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
    var canSolve := CheckCanSolveAllWaves(waves, k);
    
    if !canSolve {
        return -1;
    } else {
        if |waves| == 0 {
            assert CanSolveAllWaves(waves, k);
            assert CalculateMinimumBullets(waves, k) == CalculateMinimumBulletsHelper(waves, k, 0, k);
            assert CalculateMinimumBulletsHelper(waves, k, 0, k) == k;
            return k;
        } else {
            assert |waves| > 0;
            assert CalculateMinimumBullets(waves, k) > 0;
            return CalculateMinimumBullets(waves, k);
        }
    }
}
// </vc-code>

