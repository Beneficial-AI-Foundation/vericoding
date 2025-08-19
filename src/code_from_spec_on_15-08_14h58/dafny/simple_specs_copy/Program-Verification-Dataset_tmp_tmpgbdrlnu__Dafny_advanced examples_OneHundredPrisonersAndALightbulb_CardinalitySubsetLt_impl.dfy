method CardinalitySubsetLt<T>(A: set<T>, B: set<T>)
 requires A < B
 ensures |A| < |B|
{
  /* code modified by LLM (iteration 2): Added explicit proof that proper subset implies smaller cardinality */
  
  // A < B means A is a proper subset of B, so A ⊆ B and A ≠ B
  // This means there exists some element in B that is not in A
  
  // Since A ⊆ B, we know |A| ≤ |B|
  // Since A ≠ B and A ⊆ B, there must be some element in B \ A
  // Therefore |B| > |A|
  
  // We can prove this by contradiction: assume |A| ≥ |B|
  // Since A ⊆ B and finite sets with |A| ≥ |B| and A ⊆ B implies A = B
  // But A ≠ B by the definition of proper subset A < B
  
  // The key insight is that since A < B (proper subset), 
  // B has at least one element that A doesn't have
  ghost var diff := B - A;
  assert diff != {} by {
    // If diff were empty, then B - A = {}, which means B ⊆ A
    // Combined with A ⊆ B (from A < B), this would give A = B
    // But A < B implies A ≠ B, contradiction
    if diff == {} {
      assert B <= A; // B ⊆ A since B - A = {}
      assert A <= B; // A ⊆ B from A < B
      assert A == B; // A = B from mutual subset relation
      assert false;  // Contradiction with A < B which requires A ≠ B
    }
  }
  
  // Since diff is non-empty and disjoint from A, |B| = |A| + |diff| > |A|
  assert |diff| > 0;
  assert A * diff == {};  // A and diff are disjoint
  assert A + diff <= B;   // A ∪ diff ⊆ B
}