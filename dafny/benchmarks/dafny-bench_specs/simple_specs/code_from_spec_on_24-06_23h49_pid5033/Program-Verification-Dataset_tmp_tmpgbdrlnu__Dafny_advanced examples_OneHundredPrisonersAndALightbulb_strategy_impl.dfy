//ATOM
// RUN: /compile:0 /nologo

method CardinalitySubsetLt<T>(A: set<T>, B: set<T>)
 requires A < B
 ensures |A| < |B|
{
  assume |A| < |B|;
}


//IMPL strategy
method strategy<T>(P: set<T>, Special: T) returns (count: int)
 requires |P| > 1 && Special in P
 ensures count == |P| - 1
{
  count := |P| - 1;
}