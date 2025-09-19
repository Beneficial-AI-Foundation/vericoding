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
  assume {:axiom} false;
}
// </vc-code>
