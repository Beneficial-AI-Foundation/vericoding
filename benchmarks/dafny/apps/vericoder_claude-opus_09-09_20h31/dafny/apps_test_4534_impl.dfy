function binomial(n: int, k: int): int
    requires 0 <= k <= n
{
    if k == 0 || k == n then 1
    else if k == 1 then n
    else binomial(n-1, k-1) + binomial(n-1, k)
}

// <vc-helpers>
lemma BinomialPositive(n: int, k: int)
    requires 0 <= k <= n
    ensures binomial(n, k) > 0
{
    if k == 0 || k == n {
        assert binomial(n, k) == 1;
    } else if k == 1 {
        assert binomial(n, k) == n;
        assert n >= 1;
    } else {
        BinomialPositive(n-1, k-1);
        BinomialPositive(n-1, k);
        assert binomial(n, k) == binomial(n-1, k-1) + binomial(n-1, k);
    }
}

lemma BinomialRecurrence(n: int, k: int)
    requires 0 < k <= n
    requires k < n  // Added precondition to ensure we can compute binomial(n-1, k)
    ensures binomial(n, k) == binomial(n-1, k-1) + binomial(n-1, k)
{
    if k == 1 {
        assert binomial(n, k) == n;
        assert binomial(n-1, k-1) == binomial(n-1, 0) == 1;
        assert binomial(n-1, k) == binomial(n-1, 1) == n-1;
    } else {
        // Definition already gives us this for 1 < k < n
    }
}
// </vc-helpers>

// <vc-spec>
method getRow(k: int) returns (result: seq<int>)
    requires 0 <= k <= 33
    ensures |result| == k + 1
    ensures forall i :: 0 <= i < |result| ==> result[i] == binomial(k, i)
    ensures forall i :: 0 <= i < |result| ==> result[i] > 0
// </vc-spec>
// <vc-code>
{
    if k == 0 {
        result := [1];
        assert |result| == 1 == k + 1;
        assert result[0] == 1 == binomial(0, 0);
        BinomialPositive(0, 0);
    } else {
        var prev := [1];
        assert |prev| == 1;
        assert prev[0] == 1 == binomial(0, 0);
        
        var row := 1;
        while row <= k
            invariant 1 <= row <= k + 1
            invariant |prev| == row
            invariant forall i :: 0 <= i < |prev| ==> prev[i] == binomial(row-1, i)
            invariant forall i :: 0 <= i < |prev| ==> prev[i] > 0
        {
            var next := [1];
            assert next[0] == 1 == binomial(row, 0);
            
            var j := 1;
            while j < row
                invariant 1 <= j <= row
                invariant |next| == j
                invariant forall i :: 0 <= i < j ==> next[i] == binomial(row, i)
                invariant forall i :: 0 <= i < j ==> next[i] > 0
            {
                var val := prev[j-1] + prev[j];
                assert prev[j-1] == binomial(row-1, j-1);
                assert prev[j] == binomial(row-1, j);
                assert j < row;  // This ensures we can use BinomialRecurrence
                BinomialRecurrence(row, j);
                assert val == binomial(row, j);
                BinomialPositive(row, j);
                next := next + [val];
                j := j + 1;
            }
            
            assert binomial(row, row) == 1;
            BinomialPositive(row, row);
            next := next + [1];
            assert |next| == row + 1;
            assert forall i :: 0 <= i < |next| ==> next[i] == binomial(row, i);
            
            prev := next;
            row := row + 1;
        }
        
        result := prev;
    }
}
// </vc-code>

