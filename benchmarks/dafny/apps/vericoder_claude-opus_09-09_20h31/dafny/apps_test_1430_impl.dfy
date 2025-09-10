predicate ValidInput(N: int, K: int, S: string)
{
    N > 0 && K >= 0 && |S| == N && 
    forall i :: 0 <= i < |S| ==> S[i] == '0' || S[i] == '1'
}

function StringToBits(S: string): seq<int>
    requires forall i :: 0 <= i < |S| ==> S[i] == '0' || S[i] == '1'
{
    seq(|S|, i requires 0 <= i < |S| => if S[i] == '0' then 0 else 1)
}

predicate ValidResult(result: int, N: int)
{
    0 <= result <= N
}

// <vc-helpers>
lemma StringToBitsCount(S: string)
    requires forall i :: 0 <= i < |S| ==> S[i] == '0' || S[i] == '1'
    ensures |StringToBits(S)| == |S|
{
    // This follows directly from the definition of StringToBits
}

function CountOnes(bits: seq<int>): int
    requires forall i :: 0 <= i < |bits| ==> bits[i] == 0 || bits[i] == 1
    ensures 0 <= CountOnes(bits) <= |bits|
{
    if |bits| == 0 then 0
    else bits[0] + CountOnes(bits[1..])
}

lemma CountOnesInRange(bits: seq<int>)
    requires forall i :: 0 <= i < |bits| ==> bits[i] == 0 || bits[i] == 1
    ensures 0 <= CountOnes(bits) <= |bits|
{
    if |bits| == 0 {
        // Base case: empty sequence
    } else {
        // Inductive case
        assert bits[0] == 0 || bits[0] == 1;
        CountOnesInRange(bits[1..]);
        assert CountOnes(bits[1..]) <= |bits[1..]|;
        assert |bits[1..]| == |bits| - 1;
    }
}
// </vc-helpers>

// <vc-spec>
method solve(N: int, K: int, S: string) returns (result: int)
    requires ValidInput(N, K, S)
    ensures ValidResult(result, N)
// </vc-spec>
// <vc-code>
{
    var bits := StringToBits(S);
    StringToBitsCount(S);
    assert |bits| == N;
    
    // Verify that bits contains only 0s and 1s
    assert forall i :: 0 <= i < |bits| ==> bits[i] == 0 || bits[i] == 1;
    
    result := CountOnes(bits);
    
    // Use the lemma to establish the postcondition
    CountOnesInRange(bits);
    assert 0 <= result <= |bits|;
    assert |bits| == N;
    assert 0 <= result <= N;
}
// </vc-code>

