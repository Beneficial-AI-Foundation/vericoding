// <vc-preamble>
// Float type to match IEEE Float from Lean source
type Float = real

// Vector type for sized arrays
datatype Vector<T> = Vector(data: seq<T>, size: nat)
{
    predicate Valid() { |data| == size }
}

// Option datatype for optional weights parameter
datatype Option<T> = None | Some(value: T)

// Helper ghost function to compute sum of a vector
ghost function Sum(v: Vector<Float>): Float
    requires v.Valid()
{
    if v.size == 0 then 0.0
    else v.data[0] + Sum(Vector(v.data[1..], v.size - 1))
}

// Helper ghost function to compute dot product of two vectors
ghost function DotProduct(a: Vector<Float>, b: Vector<Float>): Float
    requires a.Valid() && b.Valid()
    requires a.size == b.size
{
    if a.size == 0 then 0.0
    else a.data[0] * b.data[0] + DotProduct(Vector(a.data[1..], a.size - 1), Vector(b.data[1..], b.size - 1))
}

// Main method implementing numpy.average functionality
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method Average(a: Vector<Float>, weights: Option<Vector<Float>>) returns (result: Float)
    // Array must be non-empty and valid
    requires a.Valid() && a.size > 0
    // If weights provided, must be valid and have same size as input array
    requires weights.Some? ==> weights.value.Valid() && weights.value.size == a.size
    // If weights provided, their sum must be non-zero to avoid division by zero
    requires weights.Some? ==> Sum(weights.value) != 0.0
    // When no weights provided, return arithmetic mean
    ensures weights.None? ==> result == Sum(a) / (a.size as Float)
    // When weights provided, return weighted average: sum(a * weights) / sum(weights)
    ensures weights.Some? ==> result == DotProduct(a, weights.value) / Sum(weights.value)
// </vc-spec>
// <vc-code>
{
  assume {:axiom} false;
}
// </vc-code>
