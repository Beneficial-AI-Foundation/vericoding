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
function Pow2(k: int): int
    requires k >= 0
    ensures Pow2(k) > 0
{
    if k == 0 then 1 else 2 * Pow2(k-1)
}

function IsPowerOfTwo(n: int): bool
    requires n > 0
{
    (n & (n - 1)) == 0
}

lemma lemma_Pow2_is_power_of_two(k: int)
    requires k >= 0
    ensures IsPowerOfTwo(Pow2(k))
{
    if k == 0 {
        assert Pow2(0) == 1;
        assert (1 & (1-1)) == 0;
    } else {
        lemma_Pow2_is_power_of_two(k-1); // Recursive call to establish IsPowerOfTwo(Pow2(k-1))
        var m := Pow2(k-1);
        assert Pow2(k) == 2 * m;
        // We know IsPowerOfTwo(m), meaning m = 2^j for some j >= 0.
        // We need to show IsPowerOfTwo(2*m), meaning 2*m = 2^(j+1).
        // This holds by definition.
        // The property of IsPowerOfTwo is that n & (n-1) == 0.
        // If m = 2^j, then 2m = 2^(j+1).
        // (2^(j+1)) & (2^(j+1) - 1) == 0 because 2^(j+1)-1 is a sequence of j+1 ones in binary.
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
    var b := StringToBits(S);
    var max_length := 0;
    var left := 0;
    var num_ones := 0;
    var i := 0; // right pointer
    while i < N
        invariant 0 <= left <= i <= N
        invariant 0 <= num_ones
        invariant num_ones <= K + 1 // num_ones can exceed K momentarily before left pointer moves
        invariant (calc sum j : int :: if left <= j < i && b[j] == 1 then 1 else 0) == num_ones
        invariant 0 <= max_length <= N
        decreases N - i
    {
        if b[i] == 1 {
            num_ones := num_ones + 1;
        }

        while num_ones > K
            invariant left <= i
            invariant (calc sum j : int :: if left <= j < i && b[j] == 1 then 1 else 0) == num_ones
            invariant num_ones > K
            decreases i - left
        {
            if b[left] == 1 {
                num_ones := num_ones - 1;
            }
            left := left + 1;
        }

        // Now, the window `[left, i]` is valid (num_ones <= K)
        // Check if its length is a power of 2 and if it's the new max.
        var current_window_length := i - left + 1;
        if current_window_length > 0 && IsPowerOfTwo(current_window_length) && current_window_length > max_length {
             max_length := current_window_length;
        }
        i := i + 1;
    }

    result := max_length;
}
// </vc-code>

