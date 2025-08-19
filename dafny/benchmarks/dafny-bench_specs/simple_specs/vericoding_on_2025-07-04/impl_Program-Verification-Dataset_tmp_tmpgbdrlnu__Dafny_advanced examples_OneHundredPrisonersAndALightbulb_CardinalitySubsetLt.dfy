//IMPL
// RUN: /compile:0 /nologo

method CardinalitySubsetLt<T>(A: set<T>, B: set<T>)
 requires A < B
 ensures |A| < |B|
{
  /* code modified by LLM (iteration 3): Fixed set union syntax from + to | and corrected set operations */
  assert A <= B;
  assert A != B;
  
  // Since A < B, there exists an element in B that's not in A
  var diff := B - A;
  assert diff != {};
  
  // Pick a witness element from the difference
  var witness :| witness in diff;
  assert witness in B;
  assert witness !in A;
  
  // The set A | {witness} is a subset of B and has one more element than A
  var A_extended := A | {witness};
  assert A_extended <= B;
  assert |A_extended| == |A| + 1;
  assert |A_extended| <= |B|;
  
  // Therefore |A| < |B|
  assert |A| + 1 <= |B|;
}