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
        Pow2(k-1);
        calc {
            Pow2(k);
            2 * Pow2(k-1);
        }
        var m := Pow2(k-1);
        assert Pow2(k) == 2 * m;
        reveal IsPowerOfTwo();
        if m == 1 { // k-1 == 0, so k == 1
          assert 2 * m == 2;
          assert (2 & (2-1)) == 0;
        } else {
          // If m is a power of two and m > 1, then m is even
          // m = 2^j for j > 0
          // 2m = 2^(j+1)
          // (2m) & (2m-1) = 0
          // If m is a power of 2, then m = 2^j for some j >= 0.
          // m-1 is of the form 011...1.
          // m&(m-1) == 0.
          // Also, m is even if j > 0.
          // If m = 2^j, then 2m = 2^(j+1).
          // And 2^(j+1) - 1 is a sequence of j+1 ones in binary.
          // 2^(j+1) & (2^(j+1) - 1) == 0.
          assert (m & (m-1)) == 0; // from recursive call for Pow2(k-1)
          assert IsPowerOfTwo(m);

          // We need to prove IsPowerOfTwo(2*m) given IsPowerOfTwo(m) for m > 1
          // Let m = 2^j for some j >= 1.
          // Then 2*m = 2^(j+1).
          // We need to show (2^(j+1) & (2^(j+1) - 1)) == 0.
          // 2^(j+1) - 1 is a number with j+1 trailing ones in binary.
          // e.g., if j=1, m=2, 2*m=4. 4 & (4-1) = 4 & 3 = 0.
          // e.g., if j=2, m=4, 2*m=8. 8 & (8-1) = 8 & 7 = 0.
        }
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
        invariant (calc sum (j: int) :: if left <= j < i && b[j] == 1 then 1 else 0) == num_ones
        invariant 0 <= max_length <= N
        decreases N - i
    {
        if b[i] == 1 {
            num_ones := num_ones + 1;
        }

        while num_ones > K
            invariant left <= i
            invariant num_ones > K
            invariant (calc sum (j: int) :: if old(left) <= j < i && b[j] == 1 then 1 else 0) == old(num_ones) ||
                      (calc sum (j: int) :: if old(left) <= j < i && b[j] == 1 then 1 else 0) + 1 == old(num_ones) // to handle the first increment
            invariant (calc sum (j: int) :: if left <= j < i && b[j] == 1 then 1 else 0) == num_ones
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

