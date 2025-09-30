predicate ValidInput(n: int, heights: seq<int>)
{
    n > 0 && |heights| == n &&
    (forall i :: 0 <= i < n ==> heights[i] >= 0) &&
    (forall i :: 0 <= i < n-1 ==> heights[i] < heights[i+1])
}

predicate ValidOutput(n: int, result: seq<int>)
{
    |result| == n &&
    (forall i :: 0 <= i < n ==> result[i] >= 0) &&
    (forall i :: 0 <= i < n-1 ==> result[i] <= result[i+1]) &&
    (forall i :: 0 <= i < n-1 ==> result[i+1] - result[i] <= 1)
}

predicate IsStable(result: seq<int>)
{
    forall i :: 0 <= i < |result|-1 ==> !(result[i] + 2 <= result[i+1])
}

function sum_seq(s: seq<int>): int
{
    if |s| == 0 then 0 else s[0] + sum_seq(s[1..])
}

// <vc-helpers>
lemma sum_seq_append(s1: seq<int>, s2: seq<int>)
    ensures sum_seq(s1 + s2) == sum_seq(s1) + sum_seq(s2)
{
    if |s1| == 0 {
        assert s1 + s2 == s2;
    } else {
        calc {
            sum_seq(s1 + s2);
            == (s1 + s2)[0] + sum_seq((s1 + s2)[1..]);
            == { assert (s1 + s2)[0] == s1[0]; 
                 assert (s1 + s2)[1..] == s1[1..] + s2; }
               s1[0] + sum_seq(s1[1..] + s2);
            == { sum_seq_append(s1[1..], s2); }
               s1[0] + sum_seq(s1[1..]) + sum_seq(s2);
            == sum_seq(s1) + sum_seq(s2);
        }
    }
}

lemma sum_seq_single(x: int)
    ensures sum_seq([x]) == x
{
}

lemma sum_seq_repeat(x: int, n: nat)
    ensures sum_seq(seq(n, i => x)) == n * x
{
    if n == 0 {
    } else {
        var s := seq(n, i => x);
        assert s == [x] + seq(n-1, i => x);
        sum_seq_append([x], seq(n-1, i => x));
        sum_seq_single(x);
        sum_seq_repeat(x, n-1);
    }
}

lemma sum_seq_non_negative(s: seq<int>)
    requires forall i :: 0 <= i < |s| ==> s[i] >= 0
    ensures sum_seq(s) >= 0
{
    if |s| == 0 {
    } else {
        assert s[0] >= 0;
        sum_seq_non_negative(s[1..]);
    }
}
// </vc-helpers>

// <vc-spec>
method solve(n: int, heights: seq<int>) returns (result: seq<int>)
    requires ValidInput(n, heights)
    ensures ValidOutput(n, result)
    ensures sum_seq(result) == sum_seq(heights)
    ensures IsStable(result)
// </vc-spec>
// <vc-code>
{
    var total := sum_seq(heights);
    
    // Prove total is non-negative
    sum_seq_non_negative(heights);
    assert total >= 0;
    
    var base := total / n;
    var remainder := total % n;
    
    // Prove base is non-negative
    assert base >= 0;
    assert remainder >= 0;
    
    result := seq(n, i => if i < n - remainder then base else base + 1);
    
    // Prove all elements are non-negative
    assert forall i :: 0 <= i < n ==> result[i] >= 0;
    
    // Prove that sum is preserved
    var low_part := seq(n - remainder, i => base);
    var high_part := seq(remainder, i => base + 1);
    assert result == low_part + high_part;
    
    sum_seq_repeat(base, n - remainder);
    assert sum_seq(low_part) == (n - remainder) * base;
    
    sum_seq_repeat(base + 1, remainder);
    assert sum_seq(high_part) == remainder * (base + 1);
    
    sum_seq_append(low_part, high_part);
    assert sum_seq(result) == sum_seq(low_part) + sum_seq(high_part);
    assert sum_seq(result) == (n - remainder) * base + remainder * (base + 1);
    assert sum_seq(result) == n * base - remainder * base + remainder * base + remainder;
    assert sum_seq(result) == n * base + remainder;
    assert sum_seq(result) == total;
}
// </vc-code>

