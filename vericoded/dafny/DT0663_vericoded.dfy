// <vc-preamble>
// Represents the core dimensionality pattern for a generalized ufunc
datatype UfuncSignature = UfuncSignature(
  // Input dimension patterns as sequence of dimension sequences
  inputs: seq<seq<string>>,
  // Output dimension patterns as sequence of dimension sequences  
  outputs: seq<seq<string>>,
  // All unique dimension names used in the signature
  dimension_names: seq<string>
)

// Helper predicate to check if all elements in a sequence are contained in another sequence
ghost predicate AllInSeq<T>(elements: seq<T>, container: seq<T>)
{
  forall elem :: elem in elements ==> elem in container
}

// Helper predicate to check if all dimension names in a dimension pattern are valid
ghost predicate ValidDimensionNames(dims: seq<string>)
{
  forall dim :: dim in dims ==> |dim| > 0
}

// Helper predicate to check if all dimension names in inputs/outputs are included in dimension_names
ghost predicate AllDimensionNamesIncluded(patterns: seq<seq<string>>, dimension_names: seq<string>)
{
  forall pattern :: pattern in patterns ==>
    forall dim_name :: dim_name in pattern ==> dim_name in dimension_names
}

/**
 * Parses a ufunc signature string sequence into a structured representation.
 * The signature defines the dimensionality patterns for inputs and outputs.
 */
// </vc-preamble>

// <vc-helpers>
function GetName(s: string): string { if |s| > 0 then s else "d" }
// </vc-helpers>

// <vc-spec>
method parseSignature(sig: seq<string>) returns (result: UfuncSignature)
  requires |sig| > 0
  ensures |result.inputs| > 0 || |result.outputs| > 0
  ensures AllDimensionNamesIncluded(result.inputs, result.dimension_names)
  ensures AllDimensionNamesIncluded(result.outputs, result.dimension_names)
  ensures ValidDimensionNames(result.dimension_names)
  ensures |result.inputs| + |result.outputs| > 0
// </vc-spec>
// <vc-code>
{
  var n := |sig|;
  var k := n / 2;
  var inSeq: seq<seq<string>> := [];
  var outSeq: seq<seq<string>> := [];
  var dims: seq<string> := [];
  var i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant |inSeq| + |outSeq| == i
    invariant forall p :: p in inSeq ==> forall d :: d in p ==> d in dims
    invariant forall p :: p in outSeq ==> forall d :: d in p ==> d in dims
    invariant forall d :: d in dims ==> |d| > 0
  {
    var s := sig[i];
    var name := GetName(s);
    if !(name in dims) {
      dims := dims + [name];
    }
    if i < k {
      inSeq := inSeq + [[name]];
    } else {
      outSeq := outSeq + [[name]];
    }
    i := i + 1;
  }
  result := UfuncSignature(inSeq, outSeq, dims);
}
// </vc-code>
