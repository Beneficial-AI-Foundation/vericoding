// RUN: %dafny /compile:0 /print:"%t.print" /dprint:"%t.dprint" /printTooltips "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

// This file shows how to specify and implement a function to compute the
// largest element of a list. The function is fully specified by two
// preconditions, as proved by the MaximumIsUnique lemma below.

// <vc-helpers>
lemma MaximumIsUnique(values: seq<int>, m1: int, m2: int)
  requires values != []
  requires m1 in values
  requires (forall i | 0 <= i < |values| :: values[i] <= m1)
  requires m2 in values
  requires (forall i | 0 <= i < |values| :: values[i] <= m2)
  ensures m1 == m2
{
  // Proof goes here. This lemma is already established by the `ensures` clauses
  // of the `Maximum` method, which is what we need for verification.
  // The lemma states that if two values m1 and m2 both satisfy the postconditions
  // of Maximum, then m1 and m2 must be equal.

  // To prove this, we can use the properties given:
  // 1. m1 is in values.
  // 2. All elements in values are less than or equal to m1.
  // 3. m2 is in values.
  // 4. All elements in values are less than or equal to m2.

  // From 2, since m2 is in values (from 3), we must have m2 <= m1.
  // The by clause needs to be a proof.
  // assert m2 <= m1 by (forall i | 0 <= i < |values| :: values[i] <= m1) && (m2 in values);
  assert (forall i | 0 <= i < |values| :: values[i] <= m1); // This is given
  assert m2 in values; // This is given
  calc {
    m2;
    <= m1; {
      // Since m2 is in values, and all elements in values are <= m1, then m2 <= m1.
      var j : int :| 0 <= j < |values| && values[j] == m2; // Changed `ensures` to `:|` for existential quantifier
      /*
      This `by` block is inside a `calc` statement, which is a bit special.
      The `calc` statement itself provides the framework for the proof.
      Dafny's verifier will try to prove the step `m2 <= m1`.
      The proof that `m2 <= m1` comes from the facts `m2 in values` and `forall i :: values[i] <= m1`.
      No explicit `assert` or `by` clause is strictly needed here if the verifier can deduce it.
      The `var j` declaration here is a way to tell Dafny "there exists such a `j`".
      */
      assert values[j] <= m1; // This specific assertion confirms what we need.
    }
  }

  // From 4, since m1 is in values (from 1), we must have m1 <= m2.
  // The by clause needs to be a proof.
  // assert m1 <= m2 by (forall i | 0 <= i < |values| :: values[i] <= m2) && (m1 in values);
  assert (forall i | 0 <= i < |values| :: values[i] <= m2); // This is given
  assert m1 in values; // This is given
  calc {
    m1;
    <= m2; {
      // Since m1 is in values, and all elements in values are <= m2, then m1 <= m2.
      var k : int :| 0 <= k < |values| && values[k] == m1; // Changed `ensures` to `:|` for existential quantifier
      assert values[k] <= m2; // This specific assertion confirms what we need.
    }
  }

  // If m2 <= m1 and m1 <= m2, then m1 must be equal to m2.
  assert m1 == m2;
}
// </vc-helpers>

// <vc-spec>
method Maximum(values: seq<int>) returns (max: int)
  requires values != []
  ensures max in values
  ensures forall i | 0 <= i < |values| :: values[i] <= max
// </vc-spec>
// <vc-code>
{
  var max_val := values[0];
  var i := 1;
  while i < |values|
    invariant 0 <= i <= |values|
    invariant max_val in values[0..i]
    invariant forall k | 0 <= k < i :: values[k] <= max_val
    decreases |values| - i
  {
    if values[i] > max_val {
      max_val := values[i];
    }
    i := i + 1;
  }
  return max_val;
}
// </vc-code>

