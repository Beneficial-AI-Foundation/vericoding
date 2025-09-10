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
    // Ensure the needed arithmetic facts are visible to the verifier
    assert 0 <= len - 1;
    assert len - 1 <= |a|;
    assert len - 1 <= |b|;

    var S := set i | 0 <= i < len && a[i] == ac && b[i] == bc;
    var Sprev := set i | 0 <= i < len - 1 && a[i] == ac && b[i] == bc;
    var x := len - 1;

    if a[x] == ac && b[x] == bc {
        // Show S == Sprev ∪ {x}

        // 1) S ⊆ Sprev ∪ {x}
        assert forall i :: i in S ==> i in Sprev || i == x;
        {
            // Provide a local proof for the universal claim
            var i := arbitrary<int>;
            assume i in S;
            // i in S means 0 <= i < len and predicate holds
            assert 0 <= i;
            assert i < len;
            if i == x {
                assert i == x;
            } else {
                // i < len and i != len-1 implies i < len-1
                assert i < len - 1;
                assert i in Sprev;
            }
        }

        // 2) Sprev ∪ {x} ⊆ S
        assert forall i :: i in Sprev || i == x ==> i in S;
        {
            var i := arbitrary<int>;
            assume i in Sprev || i == x;
            if i == x {
                // by case condition, predicate holds at x
                assert a[x] == ac && b[x] == bc;
                assert 0 <= x;
                assert x < len;
                assert i in S;
            } else {
                // i in Sprev implies 0 <= i < len-1 and predicate holds
                assert 0 <= i;
                assert i < len - 1;
                assert i < len;
                assert a[i] == ac && b[i] == bc;
                assert i in S;
            }
        }

        // From mutual inclusion, sets are equal
        assert S == Sprev + { x };

        // Now reason about cardinalities. Since x ∉ Sprev (by bounds), the union is disjoint.
        assert { x } ∩ Sprev == {};
        // Cardinality of singleton
        assert |{ x }| == 1;
        // Use that for disjoint sets |A ∪ B| = |A| + |B|
        assert |S| == |Sprev + { x }|;
        assert |Sprev + { x }| == |Sprev| + |{ x }|;
        assert |S| == |Sprev| + 1;

        // Conclude the required equality
        assert CountPositions(a, b, ac, bc, len) == CountPositions(a, b, ac, bc, len - 1) + 1;
    } else {
        // The last position does not satisfy the predicate, so sets are equal.
        assert forall i :: i in S ==> i in Sprev;
        {
            var i := arbitrary<int>;
            assume i in S;
            assert 0 <= i;
            assert i < len;
            // since a[x] != ac || b[x] != bc, index x is not in S; so any i in S must be < x
            if i == x {
                // Contradiction: if i == x then predicate would hold, but it does not. So this case cannot happen.
                assert false;
            } else {
                assert i < len - 1;
                assert i in Sprev;
            }
        }
        assert forall i :: i in Sprev ==> i in S;
        {
            var i := arbitrary<int>;
            assume i in Sprev;
            assert 0 <= i;
            assert i < len - 1;
            assert i < len;
            assert a[i] == ac && b[i] == bc;
            assert i in S;
        }
        assert S == Sprev;
        assert CountPositions(a, b, ac, bc, len) == CountPositions(a, b, ac, bc, len - 1);
        assert CountPositions(a, b, ac, bc, len) ==
               CountPositions(a, b, ac, bc, len - 1) + (if a[x] == ac && b[x] == bc then 1 else 0);
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

