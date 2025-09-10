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
lemma BitStringProperties(S: string)
    requires forall i :: 0 <= i < |S| ==> S[i] == '0' || S[i] == '1'
    ensures 0 <= |StringToBits(S)| == |S|
    ensures forall i :: 0 <= i < |StringToBits(S)| ==> StringToBits(S)[i] == 0 || StringToBits(S)[i] == 1
{
    assert |StringToBits(S)| == |S|;
    forall i | 0 <= i < |StringToBits(S)| 
        ensures StringToBits(S)[i] == 0 || StringToBits(S)[i] == 1
    {
        assert StringToBits(S)[i] == (if S[i]=='0' then 0 else 1);
    }
}

lemma ValidResultImpliesBound(result: int, N: int)
    requires ValidResult(result, N)
    ensures 0 <= result <= N
{
}

lemma LemmaMaxConsecutiveValid(maxConsecutive: int, N: int)
    requires 0 <= maxConsecutive <= N
    ensures ValidResult(maxConsecutive, N)
{
}

lemma LemmaMaxLengthValid(maxLength: int, N: int)
    requires 0 <= maxLength <= N
    ensures ValidResult(maxLength, N)
{
}

lemma LemmaMaxConsecutiveBounds(maxConsecutive: int, currentConsecutive: int, N: int)
    requires 0 <= maxConsecutive <= N && 0 <= currentConsecutive <= N
    ensures 0 <= maxConsecutive <= N && 0 <= currentConsecutive <= N
{
}
// </vc-helpers>

// <vc-spec>
method solve(N: int, K: int, S: string) returns (result: int)
    requires ValidInput(N, K, S)
    ensures ValidResult(result, N)
// </vc-spec>
// <vc-code>
{
    BitStringProperties(S);
    var bits := StringToBits(S);
    var maxConsecutive := 0;
    var currentConsecutive := 0;
    
    for i := 0 to N-1
        invariant 0 <= i <= N
        invariant 0 <= currentConsecutive <= i
        invariant 0 <= maxConsecutive <= i
        invariant maxConsecutive <= currentConsecutive || maxConsecutive <= i - currentConsecutive
    {
        if bits[i] == 1 {
            currentConsecutive := currentConsecutive + 1;
        } else {
            if currentConsecutive > maxConsecutive {
                maxConsecutive := currentConsecutive;
            }
            currentConsecutive := 0;
        }
        LemmaMaxConsecutiveBounds(maxConsecutive, currentConsecutive, N);
    }
    if currentConsecutive > maxConsecutive {
        maxConsecutive := currentConsecutive;
    }
    
    LemmaMaxConsecutiveValid(maxConsecutive, N);

    if K == 0 {
        result := maxConsecutive;
    } else {
        var left := 0;
        var right := 0;
        var currentZeros := 0;
        var maxLength := 0;
        
        while right < N
            invariant 0 <= left <= right <= N
            invariant 0 <= currentZeros <= K
            invariant 0 <= maxLength <= right - left + 1
        {
            if bits[right] == 0 {
                currentZeros := currentZeros + 1;
            }
            while currentZeros > K
                invariant left <= right
                invariant 0 <= currentZeros <= K + 1
            {
                if bits[left] == 0 {
                    currentZeros := currentZeros - 1;
                }
                left := left + 1;
            }
            if right - left + 1 > maxLength {
                maxLength := right - left + 1;
            }
            right := right + 1;
        }
        
        LemmaMaxLengthValid(maxLength, N);
        result := maxLength;
    }
    
    ValidResultImpliesBound(result, N);
}
// </vc-code>

