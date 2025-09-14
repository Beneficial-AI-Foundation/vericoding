predicate ValidInput(n: int, a: seq<int>)
{
    n >= 1 &&
    |a| == n &&
    (forall i :: 0 <= i < n ==> 1 <= a[i] <= n) &&
    (forall i, j :: 0 <= i < j < n ==> a[i] != a[j])
}

predicate ValidOutput(n: int, result: int)
{
    0 <= result <= n
}

function ReversedArray(a: seq<int>): seq<int>
    requires |a| >= 1
    ensures |ReversedArray(a)| == |a|
{
    seq(|a|, i requires 0 <= i < |a| => a[|a|-1-i])
}

predicate HasIncreasingPair(ar: seq<int>)
{
    exists i :: 1 <= i < |ar| && ar[i] > ar[i-1]
}

function CorrectResult(n: int, a: seq<int>): int
    requires ValidInput(n, a)
    ensures ValidOutput(n, CorrectResult(n, a))
{
    var ar := ReversedArray(a);
    if HasIncreasingPair(ar) then
        var min_i := MinIndex(ar, n);
        n - min_i
    else
        0
}

// <vc-helpers>
function MinIndex(ar: seq<int>, n: int): int
    requires |ar| == n
    requires n >= 1
    requires HasIncreasingPair(ar)
    ensures 1 <= MinIndex(ar, n) < n
    ensures ar[MinIndex(ar, n)] > ar[MinIndex(ar, n) - 1]
    ensures forall k :: 1 <= k < MinIndex(ar, n) ==> ar[k] <= ar[k-1]
{
    MinIndexHelper(ar, n, 1)
}

function MinIndexHelper(ar: seq<int>, n: int, i: int): int
    requires |ar| == n
    requires n >= 1
    requires 1 <= i <= n
    requires HasIncreasingPair(ar)
    requires forall k :: 1 <= k < i ==> ar[k] <= ar[k-1]
    decreases n - i
    ensures i <= MinIndexHelper(ar, n, i) < n
    ensures ar[MinIndexHelper(ar, n, i)] > ar[MinIndexHelper(ar, n, i) - 1]
    ensures forall k :: 1 <= k < MinIndexHelper(ar, n, i) ==> ar[k] <= ar[k-1]
{
    if i < n && ar[i] > ar[i-1] then
        i
    else if i < n then
        MinIndexHelper(ar, n, i+1)
    else
        // At this point i == n, but we haven't found an increasing pair
        // This contradicts HasIncreasingPair(ar)
        // We return a witness directly
        FindIncreasingPairWitness(ar, n)
}

lemma ExistsIncreasingPairBeforeN(ar: seq<int>, n: int, i: int)
    requires |ar| == n
    requires n >= 1
    requires 1 <= i <= n
    requires HasIncreasingPair(ar)
    requires forall k :: 1 <= k < i ==> ar[k] <= ar[k-1]
    ensures exists j :: i <= j < n && ar[j] > ar[j-1]
{
    // Since HasIncreasingPair(ar) holds, there exists some index where ar[idx] > ar[idx-1]
    // If all k < i have ar[k] <= ar[k-1], then the increasing pair must be at or after i
    assert exists idx :: 1 <= idx < n && ar[idx] > ar[idx-1];
}

function FindIncreasingPairWitness(ar: seq<int>, n: int): int
    requires |ar| == n
    requires n >= 1
    requires HasIncreasingPair(ar)
    ensures 1 <= FindIncreasingPairWitness(ar, n) < n
    ensures ar[FindIncreasingPairWitness(ar, n)] > ar[FindIncreasingPairWitness(ar, n) - 1]
{
    FindIncreasingPairWitnessHelper(ar, n, 1)
}

function FindIncreasingPairWitnessHelper(ar: seq<int>, n: int, i: int): int
    requires |ar| == n
    requires n >= 1
    requires 1 <= i <= n
    requires HasIncreasingPair(ar)
    requires forall k :: 1 <= k < i ==> ar[k] <= ar[k-1]
    requires i < n ==> exists j :: i <= j < n && ar[j] > ar[j-1]  // Key invariant
    decreases n - i
    ensures 1 <= FindIncreasingPairWitnessHelper(ar, n, i) < n
    ensures ar[FindIncreasingPairWitnessHelper(ar, n, i)] > ar[FindIncreasingPairWitnessHelper(ar, n, i) - 1]
{
    if i == n then
        // This case is impossible given our preconditions
        ExistsIncreasingPairBeforeN(ar, n, n);
        assert false;  // We've ruled out all positions but HasIncreasingPair is true
        1  // Unreachable, but needed for totality
    else if ar[i] > ar[i-1] then
        i
    else
        ExistsIncreasingPairBeforeN(ar, n, i+1);
        FindIncreasingPairWitnessHelper(ar, n, i+1)
}
// </vc-helpers>

// <vc-spec>
method solve(n: int, a: seq<int>) returns (result: int)
    requires ValidInput(n, a)
    ensures ValidOutput(n, result)
    ensures result == CorrectResult(n, a)
// </vc-spec>
// <vc-code>
{
    var ar := seq(n, i requires 0 <= i < n => a[n-1-i]);
    
    // Check if there's an increasing pair
    var hasIncrease := false;
    var minIndex := 0;
    
    var j := 1;
    while j < n
        invariant 1 <= j <= n
        invariant ar == ReversedArray(a)
        invariant hasIncrease ==> 1 <= minIndex < j && ar[minIndex] > ar[minIndex-1]
        invariant hasIncrease ==> forall k :: 1 <= k < minIndex ==> ar[k] <= ar[k-1]
        invariant !hasIncrease ==> forall k :: 1 <= k < j ==> ar[k] <= ar[k-1]
    {
        if ar[j] > ar[j-1] {
            if !hasIncrease {
                hasIncrease := true;
                minIndex := j;
            }
            break;
        }
        j := j + 1;
    }
    
    if hasIncrease {
        assert HasIncreasingPair(ar);
        assert minIndex == MinIndex(ar, n);
        result := n - minIndex;
    } else {
        assert !HasIncreasingPair(ar);
        result := 0;
    }
}
// </vc-code>

