// SPEC
// RUN: /compile:0 /nologo

method CardinalitySubsetLt<T>(A: set<T>, B: set<T>)
 requires A < B
 ensures |A| < |B|
{
}
