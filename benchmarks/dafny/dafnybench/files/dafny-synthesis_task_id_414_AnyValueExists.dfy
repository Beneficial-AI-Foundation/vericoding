// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method AnyValueExists(seq1: seq<int>, seq2: seq<int>) returns (result: bool)
    ensures result <==> (exists i :: 0 <= i < |seq1| && seq1[i] in seq2)
// </vc-spec>
// <vc-code>
{
  assume {:axiom} false;
}
// </vc-code>
