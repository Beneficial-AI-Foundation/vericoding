// <vc-preamble>
// Method to concatenate two sequences of real numbers
// </vc-preamble>

// <vc-helpers>

  // Helper lemma to prove element-wise equality for the concatenation
  lemma ConcatLemma(a: seq<real>, b: seq<real>, result: seq<real>)
    requires |result| == |a| + |b|
    requires forall i :: 0 <= i < |a| ==> result[i] == a[i]
    requires forall j :: 0 <= j < |b| ==> result[|a| + j] == b[j]
    ensures result == a + b
  {
    // By Dafny's built-in sequence concatenation properties
  }

// </vc-helpers>

// <vc-spec>
method Concatenate(a: seq<real>, b: seq<real>) returns (result: seq<real>)
  // Postcondition: result has length equal to sum of input lengths
  ensures |result| == |a| + |b|
  
  // Postcondition: first |a| elements of result match vector a
  ensures forall i :: 0 <= i < |a| ==> result[i] == a[i]
  
  // Postcondition: next |b| elements of result match vector b  
  ensures forall j :: 0 <= j < |b| ==> result[|a| + j] == b[j]
// </vc-spec>
// <vc-code>
{
  result := a + b;
  // Dafny's built-in sequence concatenation automatically satisfies:
  // 1. |a + b| == |a| + |b|
  // 2. forall i :: 0 <= i < |a| ==> (a + b)[i] == a[i]
  // 3. forall j :: 0 <= j < |b| ==> (a + b)[|a| + j] == b[j]
}
// </vc-code>
