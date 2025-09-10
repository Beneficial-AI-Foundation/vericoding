predicate ValidInput(A1: int, A2: int, A3: int)
{
    1 <= A1 <= 100 && 1 <= A2 <= 100 && 1 <= A3 <= 100
}

function MaxOfThree(A1: int, A2: int, A3: int): int
{
    if A1 >= A2 && A1 >= A3 then A1 else if A2 >= A3 then A2 else A3
}

function MinOfThree(A1: int, A2: int, A3: int): int
{
    if A1 <= A2 && A1 <= A3 then A1 else if A2 <= A3 then A2 else A3
}

function MinimumCost(A1: int, A2: int, A3: int): int
{
    MaxOfThree(A1, A2, A3) - MinOfThree(A1, A2, A3)
}

// <vc-helpers>
lemma MaxGeMin(A1: int, A2: int, A3: int)
  requires ValidInput(A1, A2, A3)
  ensures MaxOfThree(A1, A2, A3) - MinOfThree(A1, A2, A3) >= 0
{
  // Prove MaxOfThree >= A1
  if A1 >= A2 && A1 >= A3 {
    assert MaxOfThree(A1, A2, A3) == A1;
    assert MaxOfThree(A1, A2, A3) >= A1;
  } else if A2 >= A3 {
    assert MaxOfThree(A1, A2, A3) == A2;
    if A1 >= A3 {
      // not(A1>=A2 && A1>=A3) holds here, together with A1>=A3 implies not(A1>=A2), hence A1 < A2
      assert !(A1 >= A2 && A1 >= A3);
      assert A1 >= A3;
      assert !(A1 >= A2);
      assert A1 < A2;
      assert A2 > A1;
    } else {
      // A1 < A3 and A2 >= A3  => A2 > A1
      assert A1 < A3;
      assert A2 >= A3;
      assert A2 > A1;
    }
    assert MaxOfThree(A1, A2, A3) >= A1;
  } else {
    // Max = A3
    assert MaxOfThree(A1, A2, A3) == A3;
    if A1 >= A2 {
      // not(A1>=A2 && A1>=A3) and A1>=A2 implies not(A1>=A3) so A1 < A3
      assert !(A1 >= A2 && A1 >= A3);
      assert A1 >= A2;
      assert !(A1 >= A3);
      assert A1 < A3;
      assert A3 > A1;
    } else {
      // A1 < A2 and A3 > A2 (since else branch of A2>=A3) => A3 > A1
      assert A1 < A2;
      assert A3 > A2;
      assert A3 > A1;
    }
    assert MaxOfThree(A1, A2, A3) >= A1;
  }

  // Prove MinOfThree <= A1
  if A1 <= A2 && A1 <= A3 {
    assert MinOfThree(A1, A2, A3) == A1;
    assert MinOfThree(A1, A2, A3) <= A1;
  } else if A2 <= A3 {
    assert MinOfThree(A1, A2, A3) == A2;
    if A1 <= A3 {
      // not(A1<=A2 && A1<=A3) together with A1<=A3 implies not(A1<=A2) i.e. A1 > A2
      assert !(A1 <= A2 && A1 <= A3);
      assert A1 <= A3;
      assert !(A1 <= A2);
      assert A1 > A2;
    } else {
      // A1 > A3 and A2 <= A3 => A2 < A1
      assert A1 > A3;
      assert A2 <= A3;
      assert A2 < A1;
    }
    assert MinOfThree(A1, A2, A3) <= A1;
  } else {
    assert MinOfThree(A1, A2, A3) == A3;
    if A1 <= A2 {
      // not(A1<=A2 && A1<=A3) and A1<=A2 implies not(A1<=A3) => A1 > A3
      assert !(A1 <= A2 && A1 <= A3);
      assert A1 <= A2;
      assert !(A1 <= A3);
      assert A1 > A3;
    } else {
      // A1 > A2 and (else of A2<=A3) gives A2 > A3, so A1 > A3
      assert !(A1 <= A2 && A1 <= A3);
      assert !(A2 <= A3);
      assert A1 > A2;
      assert A2 > A3;
      assert A1 > A3;
    }
    assert MinOfThree(A1, A2, A3) <= A1;
  }

  // From above Max >= A1 and Min <= A1, conclude Max >= Min
  assert MaxOfThree(A1, A2, A3) >= MinOfThree(A1, A2, A3);
  assert MaxOfThree(A1, A2, A3) - MinOfThree(A1, A2, A3) >= 0;
}
// </vc-helpers>

// <vc-spec>
method solve(A1: int, A2: int, A3: int) returns (result: int)
    requires ValidInput(A1, A2, A3)
    ensures result >= 0
    ensures result == MinimumCost(A1, A2, A3)
// </vc-spec>
// <vc-code>
{
  MaxGeMin(A1, A2, A3);
  result := MaxOfThree(A1, A2, A3) - MinOfThree(A1, A2, A3);
}
// </vc-code>

