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
lemma CountPositionsIncr(a: string, b: string, ac: char, bc: char, len: int)
    requires 0 < len && len <= |a| && len <= |b|
    requires ac == '0' || ac == '1'
    requires bc == '0' || bc == '1'
    ensures CountPositions(a, b, ac, bc, len) ==
            CountPositions(a, b, ac, bc, len - 1) + (if a[len - 1] == ac && b[len - 1] == bc then 1 else 0)
{
    // Unfold the definition of CountPositions based on the set comprehension.
    // The set { i | 0 <= i < len && P(i) } is either the set for len-1
    // plus the element len-1 when P(len-1) holds.
    assert CountPositions(a, b, ac, bc, len) ==
           |set i | 0 <= i < len - 1 && a[i] == ac && b[i] == bc|
           + (if a[len - 1] == ac && b[len - 1] == bc then 1 else 0);
    // Recognize the first term as CountPositions(..., len-1)
    assert |set i | 0 <= i < len - 1 && a[i] == ac && b[i] == bc| ==
           CountPositions(a, b, ac, bc, len - 1);
}

lemma CountNonNeg(a: string, b: string, ac: char, bc: char, len: int)
    requires 0 <= len && len <= |a| && len <= |b|
    requires ac == '0' || ac == '1'
    requires bc == '0' || bc == '1'
    ensures CountPositions(a, b, ac, bc, len) >= 0
{
    if len == 0 {
        assert CountPositions(a, b, ac, bc, 0) == 0;
    } else {
        CountNonNeg(a, b, ac, bc, len - 1);
        calc {
            CountPositions(a, b, ac, bc, len);
            ==;
            CountPositions(a, b, ac, bc, len - 1) + (if a[len - 1] == ac && b[len - 1] == bc then 1 else 0);
            >=;
            0 + 0;
            ==;
            0;
        }
    }
}

lemma PartitionCountsLen(a: string, b: string, len: int)
    requires 0 <= len && len <= |a| && len <= |b|
    requires (forall i :: 0 <= i < |a| ==> a[i] == '0' || a[i] == '1')
    requires (forall i :: 0 <= i < |b| ==> b[i] == '0' || b[i] == '1')
    ensures CountPositions(a, b, '0', '0', len) +
            CountPositions(a, b, '0', '1', len) +
            CountPositions(a, b, '1', '0', len) +
            CountPositions(a, b, '1', '1', len) == len
    decreases len
{
    if len == 0 {
        assert CountPositions(a, b, '0', '0', 0) == 0;
        assert CountPositions(a, b, '0', '1', 0) == 0;
        assert CountPositions(a, b, '1', '0', 0) == 0;
        assert CountPositions(a, b, '1', '1', 0) == 0;
    } else {
        PartitionCountsLen(a, b, len - 1);
        // Use the increment property for each pair type
        CountPositionsIncr(a, b, '0', '0', len);
        CountPositionsIncr(a, b, '0', '1', len);
        CountPositionsIncr(a, b, '1', '0', len);
        CountPositionsIncr(a, b, '1', '1', len);

        var inc00 := if a[len - 1] == '0' && b[len - 1] == '0' then 1 else 0;
        var inc01 := if a[len - 1] == '0' && b[len - 1] == '1' then 1 else 0;
        var inc10 := if a[len - 1] == '1' && b[len - 1] == '0' then 1 else 0;
        var inc11 := if a[len - 1] == '1' && b[len - 1] == '1' then 1 else 0;

        // Exactly one of the inc's is 1, the rest are 0.
        assert inc00 + inc01 + inc10 + inc11 == 1;

        // Add the equalities and use the induction hypothesis.
        assert
            CountPositions(a, b, '0', '0', len - 1) +
            CountPositions(a, b, '0', '1', len - 1) +
            CountPositions(a, b, '1', '0', len - 1) +
            CountPositions(a, b, '1', '1', len - 1) == len - 1;

        assert
            CountPositions(a, b, '0', '0', len) +
            CountPositions(a, b, '0', '1', len) +
            CountPositions(a, b, '1', '0', len) +
            CountPositions(a, b, '1', '1', len) ==
            (CountPositions(a, b, '0', '0', len - 1) + inc00) +
            (CountPositions(a, b, '0', '1', len - 1) + inc01) +
            (CountPositions(a, b, '1', '0', len - 1) + inc10) +
            (CountPositions(a, b, '1', '1', len - 1) + inc11);

        // Combine to get len.
        assert
            (CountPositions(a, b, '0', '0', len - 1) +
             CountPositions(a, b, '0', '1', len - 1) +
             CountPositions(a, b, '1', '0', len - 1) +
             CountPositions(a, b, '1', '1', len - 1)) +
            (inc00 + inc01 + inc10 + inc11) == (len - 1) + 1;
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
  var t00 := CountPositions(a, b, '0', '0', 2 * n);
  var t01 := CountPositions(a, b, '0', '1', 2 * n);
  var t10 := CountPositions(a, b, '1', '0', 2 * n);
  var t11 := CountPositions(a, b, '1', '1', 2 * n);

  // Prove non-negativity of counts
  CountNonNeg(a, b, '0', '0', 2 * n);
  CountNonNeg(a, b, '0', '1', 2 * n);
  CountNonNeg(a, b, '1', '0', 2 * n);
  CountNonNeg(a, b, '1', '1', 2 * n);

  // Prove the partition property: counts sum to 2*n
  PartitionCountsLen(a, b, 2 * n);

  var d := ComputeGameOutcome(t00, t01, t10, t11);
  if d > 0 {
    result := "First";
  } else if d < 0 {
    result := "Second";
  } else {
    result := "Draw";
  }

  // Ensure CorrectOutcome holds
  assert CorrectOutcome(result, d);

  // Provide witnesses for the existential in the postcondition
  assert exists tt00, tt01, tt10, tt11 ::
    tt00 == t00 && tt01 == t01 && tt10 == t10 && tt11 == t11 &&
    tt00 >= 0 && tt01 >= 0 && tt10 >= 0 && tt11 >= 0 &&
    tt00 + tt01 + tt10 + tt11 == 2 * n &&
    tt00 == CountPositions(a, b, '0', '0', 2 * n) &&
    tt01 == CountPositions(a, b, '0', '1', 2 * n) &&
    tt10 == CountPositions(a, b, '1', '0', 2 * n) &&
    tt11 == CountPositions(a, b, '1', '1', 2 * n) &&
    CorrectOutcome(result, ComputeGameOutcome(tt00, tt01, tt10, tt11));
}
// </vc-code>

