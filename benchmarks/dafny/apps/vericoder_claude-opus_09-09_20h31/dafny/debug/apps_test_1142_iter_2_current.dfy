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
function CalculateMinimumBulletsHelper(waves: seq<Wave>, k: nat, waveIndex: nat, bulletsInMagazine: nat): nat
    requires k > 0
    requires ValidWaves(waves)
    requires bulletsInMagazine <= k
    requires waveIndex <= |waves|
    requires CanSolveAllWaves(waves, k)
    decreases |waves| - waveIndex
    ensures waveIndex < |waves| ==> CalculateMinimumBulletsHelper(waves, k, waveIndex, bulletsInMagazine) >= waves[waveIndex].monsters - bulletsInMagazine
    ensures |waves| > 0 && waveIndex == 0 && bulletsInMagazine == k ==> CalculateMinimumBulletsHelper(waves, k, waveIndex, bulletsInMagazine) > 0
{
    if waveIndex == |waves| then
        0
    else
        var wave := waves[waveIndex];
        var bulletsNeeded := wave.monsters;
        var bulletsUsedFromCurrent := if bulletsNeeded <= bulletsInMagazine then bulletsNeeded else bulletsInMagazine;
        var bulletsFromNewMagazines := if bulletsNeeded > bulletsInMagazine then bulletsNeeded - bulletsInMagazine else 0;
        var bulletsRemainingAfter := if bulletsNeeded <= bulletsInMagazine then bulletsInMagazine - bulletsNeeded else (k - (bulletsFromNewMagazines % k)) % k;
        
        bulletsFromNewMagazines + CalculateMinimumBulletsHelper(waves, k, waveIndex + 1, bulletsRemainingAfter)
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
    // Check if we can solve all waves
    var canSolve := true;
    var i := 0;
    
    while i < |waves|
        invariant 0 <= i <= |waves|
        invariant canSolve ==> (forall j :: 0 <= j < i ==> CanSolveWave(waves, j, k))
        invariant !canSolve ==> (exists j :: 0 <= j < i && !CanSolveWave(waves, j, k))
    {
        var wave := waves[i];
        var timeAvailable := wave.end_time - wave.start_time + 1;
        var maxPossibleShots := timeAvailable * k;
        
        if wave.monsters > maxPossibleShots {
            canSolve := false;
        } else if i > 0 {
            var prevWave := waves[i - 1];
            var timeGap := wave.start_time - prevWave.end_time;
            var reloadsNeeded := if prevWave.monsters <= k then 0 else (prevWave.monsters - 1) / k;
            
            if reloadsNeeded > timeGap {
                canSolve := false;
            }
        }
        
        if canSolve && !CanSolveWave(waves, i, k) {
            canSolve := false;
        }
        
        i := i + 1;
    }
    
    assert canSolve <==> CanSolveAllWaves(waves, k);
    
    if !canSolve {
        result := -1;
    } else {
        // Calculate minimum bullets needed
        var totalBullets := 0;
        var bulletsInMagazine := k;
        var j := 0;
        
        while j < |waves|
            invariant 0 <= j <= |waves|
            invariant bulletsInMagazine <= k
            invariant CanSolveAllWaves(waves, k)
            invariant totalBullets + CalculateMinimumBulletsHelper(waves, k, j, bulletsInMagazine) == CalculateMinimumBulletsHelper(waves, k, 0, k)
        {
            var wave := waves[j];
            var bulletsNeeded := wave.monsters;
            
            if bulletsNeeded <= bulletsInMagazine {
                bulletsInMagazine := bulletsInMagazine - bulletsNeeded;
            } else {
                var bulletsFromNewMagazines := bulletsNeeded - bulletsInMagazine;
                totalBullets := totalBullets + bulletsFromNewMagazines;
                bulletsInMagazine := k - (bulletsFromNewMagazines % k);
                if bulletsInMagazine == k {
                    bulletsInMagazine := 0;
                }
            }
            
            j := j + 1;
        }
        
        result := totalBullets;
    }
}
// </vc-code>

