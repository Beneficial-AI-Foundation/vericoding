predicate ValidInput(n: int, a: string, b: string)
{
    n > 0 && |a| == 2 * n && |b| == 2 * n &&
    (forall i :: 0 <= i < |a| ==> a[i] == '0' || a[i] == '1') &&
    (forall i :: 0 <= i < |b| ==> b[i] == '0' || b[i] == '1')
}

function CountPositions(a: string, b: string, ac: char, bc: char, len: int): int
    requires len >= 0 && len <= |a| && len <= |b|
    requires ac == '0' || ac == '1'
    requires bc == '0' || bc == '1'
{
    |set i | 0 <= i < len && a[i] == ac && b[i] == bc|
}

function ComputeGameOutcome(t00: int, t01: int, t10: int, t11: int): int
{
    t11 % 2 + (t10 - t01 + 1 - t11 % 2) / 2
}

predicate CorrectOutcome(result: string, d: int)
{
    (d > 0 ==> result == "First") &&
    (d < 0 ==> result == "Second") &&
    (d == 0 ==> result == "Draw")
}

// <vc-helpers>
function CountPositions_upto_k(a: string, b: string, ac: char, bc: char, k: int): int
    requires 0 <= k <= |a| && 0 <= k <= |b|
    requires ac == '0' || ac == '1'
    requires bc == '0' || bc == '1'
    decreases k
{
    if k == 0 then 0
    else
        var prev_count := CountPositions_upto_k(a, b, ac, bc, k - 1);
        if a[k-1] == ac && b[k-1] == bc then prev_count + 1
        else prev_count
}

lemma {:induction k} CountPositions_equals_CountPositions_upto_k(a: string, b: string, ac: char, bc: char, k: int)
    requires 0 <= k <= |a| && 0 <= k <= |b|
    requires ac == '0' || ac == '1'
    requires bc == '0' || bc == '1'
    ensures CountPositions(a, b, ac, bc, k) == CountPositions_upto_k(a, b, ac, bc, k)
{
    if k == 0 {
        // Base case: k == 0
        calc {
            CountPositions(a, b, ac, bc, 0);
            |set i | 0 <= i < 0 && a[i] == ac && b[i] == bc|;
            0;
            CountPositions_upto_k(a, b, ac, bc, 0);
        }
    } else {
        // Inductive step
        CountPositions_equals_CountPositions_upto_k(a, b, ac, bc, k - 1);
        calc {
            CountPositions(a, b, ac, bc, k);
            |set i | 0 <= i < k && a[i] == ac && b[i] == bc|;
        {
            var S := set i | 0 <= i < k && a[i] == ac && b[i] == bc;
            var S_k_minus_1 := set i | 0 <= i < k-1 && a[i] == ac && b[i] == bc;
            assert S == S_k_minus_1 + (if a[k-1] == ac && b[k-1] == bc then {k-1} else {});
            assert |S| == |S_k_minus_1| + (if a[k-1] == ac && b[k-1] == bc then 1 else 0) by {
                if a[k-1] == ac && b[k-1] == bc {
                    assert S == S_k_minus_1 + {k-1};
                    assert !({k-1} in S_k_minus_1); // k-1 is not in S_k_minus_1 because 0 <= i < k-1
                    assert |S| == |S_k_minus_1| + 1;
                } else {
                    assert S == S_k_minus_1;
                    assert |S| == |S_k_minus_1|;
                }
            }
        }
            CountPositions(a, b, ac, bc, k-1) + (if a[k-1] == ac && b[k-1] == bc then 1 else 0);
            CountPositions_upto_k(a, b, ac, bc, k-1) + (if a[k-1] == ac && b[k-1] == bc then 1 else 0); // by inductive hypothesis
            CountPositions_upto_k(a, b, ac, bc, k);
        }
    }
}
// </vc-helpers>

// <vc-spec>
method solve(n: int, a: string, b: string) returns (result: string)
    requires ValidInput(n, a, b)
    ensures result == "First" || result == "Second" || result == "Draw"
    ensures (exists t00, t01, t10, t11: int ::
        t00 >= 0 && t01 >= 0 && t10 >= 0 && t11 >= 0 &&
        t00 + t01 + t10 + t11 == 2 * n &&
        t00 == CountPositions(a, b, '0', '0', 2 * n) &&
        t01 == CountPositions(a, b, '0', '1', 2 * n) &&
        t10 == CountPositions(a, b, '1', '0', 2 * n) &&
        t11 == CountPositions(a, b, '1', '1', 2 * n) &&
        CorrectOutcome(result, ComputeGameOutcome(t00, t01, t10, t11)))
// </vc-spec>
// <vc-code>
{
    var t00: int := CountPositions_upto_k(a, b, '0', '0', 2 * n);
    var t01: int := CountPositions_upto_k(a, b, '0', '1', 2 * n);
    var t10: int := CountPositions_upto_k(a, b, '1', '0', 2 * n);
    var t11: int := CountPositions_upto_k(a, b, '1', '1', 2 * n);

    lemma CountPositions_equals_CountPositions_upto_k(a, b, '0', '0', 2 * n);
    lemma CountPositions_equals_CountPositions_upto_k(a, b, '0', '1', 2 * n);
    lemma CountPositions_equals_CountPositions_upto_k(a, b, '1', '0', 2 * n);
    lemma CountPositions_equals_CountPositions_upto_k(a, b, '1', '1', 2 * n);

    assert t00 == CountPositions(a, b, '0', '0', 2 * n) by {
        lemma CountPositions_equals_CountPositions_upto_k(a, b, '0', '0', 2 * n);
    };
    assert t01 == CountPositions(a, b, '0', '1', 2 * n) by {
        lemma CountPositions_equals_CountPositions_upto_k(a, b, '0', '1', 2 * n);
    };
    assert t10 == CountPositions(a, b, '1', '0', 2 * n) by {
        lemma CountPositions_equals_CountPositions_upto_k(a, b, '1', '0', 2 * n);
    };
    assert t11 == CountPositions(a, b, '1', '1', 2 * n) by {
        lemma CountPositions_equals_CountPositions_upto_k(a, b, '1', '1', 2 * n);
    };

    // Calculate sum for all positions
    var sumPositions := 0;
    for k := 0 to 2 * n - 1
        invariant 0 <= k <= 2 * n
        invariant sumPositions == CountPositions_upto_k(a, b, '0', '0', k) + CountPositions_upto_k(a, b, '0', '1', k) +
                                  CountPositions_upto_k(a, b, '1', '0', k) + CountPositions_upto_k(a, b, '1', '1', k)
    {
        var char_a := a[k];
        var char_b := b[k];
        if char_a == '0' && char_b == '0' {
            sumPositions := sumPositions + 1;
        } else if char_a == '0' && char_b == '1' {
            sumPositions := sumPositions + 1;
        } else if char_a == '1' && char_b == '0' {
            sumPositions := sumPositions + 1;
        } else if char_a == '1' && char_b == '1' {
            sumPositions := sumPositions + 1;
        }
    }
    assert sumPositions == 2 * n;
    assert t00 + t01 + t10 + t11 == sumPositions;
    assert t00 + t01 + t10 + t11 == 2 * n;

    var d: int := ComputeGameOutcome(t00, t01, t10, t11);

    if d > 0 {
        result := "First";
    } else if d < 0 {
        result := "Second";
    } else {
        result := "Draw";
    }
}
// </vc-code>

