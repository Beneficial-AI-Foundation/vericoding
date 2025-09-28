// <vc-preamble>
// Define the different kinds of numeric types
datatype NumericKind = Integer | UnsignedInteger | Float | Complex | String | Boolean

// Define precision levels from lowest to highest
datatype Precision = P8 | P16 | P32 | P64 | P128 | P256

// A numeric type combining kind and precision
datatype NumericType = NumericType(kind: NumericKind, precision: Precision)

// Define the maximum precision available for each numeric kind
function MaxPrecisionFor(kind: NumericKind): Precision
{
    match kind
    case Integer => P64
    case UnsignedInteger => P64
    case Float => P128
    case Complex => P256
    case String => P64  // Represents max string length handling capacity
    case Boolean => P8
}

// Define precision ordering - returns true if p1 <= p2
predicate PrecisionLE(p1: Precision, p2: Precision)
{
    match (p1, p2)
    case (P8, _) => true
    case (P16, P8) => false
    case (P16, _) => true
    case (P32, P8) => false
    case (P32, P16) => false
    case (P32, _) => true
    case (P64, P8) => false
    case (P64, P16) => false
    case (P64, P32) => false
    case (P64, _) => true
    case (P128, P256) => true
    case (P128, _) => false
    case (P256, _) => false
}

// Return the scalar type of highest precision of the same kind as the input
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 4): [Added PrecisionAsInt to allow transitive reasoning on Precision] */
function PrecisionAsInt(p: Precision): int {
    match p
    case P8 => 8
    case P16 => 16
    case P32 => 32
    case P64 => 64
    case P128 => 128
    case P256 => 256
}

/* helper modified by LLM (iteration 4): [Added a lemma to prove the postcondition for valid inputs] */
lemma ProvePostconditionForValidInput(t: NumericType)
    requires PrecisionAsInt(t.precision) <= PrecisionAsInt(MaxPrecisionFor(t.kind))
    ensures PrecisionLE(t.precision, MaxPrecisionFor(t.kind))
{
    var max_p := MaxPrecisionFor(t.kind);
    if t.kind == Float {
        // max_p is P128. requires ensures t.precision <= P128.
        // If t.precision == P128, PrecisionLE(P128, P128) is false. This is a contradiction in spec.
        // The postcondition cannot be proven in this case.
    } else if t.kind == Complex {
        // max_p is P256. requires ensures t.precision <= P256.
        // If t.precision == P256, PrecisionLE(P256, P256) is false. This is a contradiction in spec.
        // The postcondition cannot be proven in this case.
    } else {
        // For all other kinds, PrecisionLE is reflexive for their MaxPrecision, and transitive.
        // So if t.precision <= MaxPrecision, PrecisionLE works.
    }
}
// </vc-helpers>

// <vc-spec>
method MaximumSctype(t: NumericType) returns (result: NumericType)
    ensures result.kind == t.kind  // Same kind as input
    ensures result.precision == MaxPrecisionFor(t.kind)  // Maximum precision for that kind
    ensures PrecisionLE(t.precision, result.precision)  // Result has higher or equal precision
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 4): [Set result and call helper, accepting verification will fail on contradictory spec] */
  result := NumericType(t.kind, MaxPrecisionFor(t.kind));
  if PrecisionAsInt(t.precision) <= PrecisionAsInt(MaxPrecisionFor(t.kind)) {
    ProvePostconditionForValidInput(t);
  }
}
// </vc-code>
