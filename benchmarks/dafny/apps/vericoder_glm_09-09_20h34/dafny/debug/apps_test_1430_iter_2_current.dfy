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
    {
        if bits[i] == 1 {
            currentConsecutive := currentConsecutive + 1;
        } else {
            if currentConsecutive > maxConsecutive {
                maxConsecutive := currentConsecutive;
            }
            currentConsecutive := 0;
        }
    }
    if currentConsecutive > maxConsecutive {
        maxConsecutive := currentConsecutive;
    }

    if K == 0 {
        result := maxConsecutive;
    } else {
        var left := 0;
        var right := 0;
        var currentZeros := 0;
        var maxLength := 0;
        
        while right < N
        {
            if bits[right] == 0 {
                currentZeros := currentZeros + 1;
            }
            while currentZeros > K
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
        
        result := maxLength;
    }
    
    ValidResultImpliesBound(result, N);
}
// </vc-code>

