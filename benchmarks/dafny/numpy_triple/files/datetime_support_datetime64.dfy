// <vc-preamble>
// Time unit enumeration for datetime64 objects
datatype TimeUnit = 
    | Years        // 'Y' - Years unit
    | Days         // 'D' - Days unit  
    | Hours        // 'h' - Hours unit
    | Minutes      // 'm' - Minutes unit
    | Seconds      // 's' - Seconds unit
    | Milliseconds // 'ms' - Milliseconds unit
    | Microseconds // 'us' - Microseconds unit
    | Nanoseconds  // 'ns' - Nanoseconds unit

// DateTime64 structure representing offset from Unix epoch
datatype DateTime64 = DateTime64(
    offset: int,      // Offset value from 1970-01-01T00:00:00
    unit: TimeUnit,   // Time unit of the offset
    isUtc: bool       // Always UTC with +0000 offset
)

// Predicate to check if a DateTime64 satisfies unit-specific validity constraints
predicate ValidDateTime64(dt: DateTime64)
{
    match dt.unit {
        case Years => dt.offset + 1970 >= 1 && dt.offset + 1970 <= 9999  // Valid year range
        case Days => dt.offset >= -2147483648 && dt.offset <= 2147483647    // Days since epoch
        case Hours => dt.offset >= -2147483648 && dt.offset <= 2147483647   // Hours since epoch
        case Minutes => dt.offset >= -2147483648 && dt.offset <= 2147483647 // Minutes since epoch
        case Seconds => dt.offset >= -2147483648 && dt.offset <= 2147483647 // Seconds since epoch
        case Milliseconds => true  // Milliseconds can use full int range
        case Microseconds => true  // Microseconds can use full int range
        case Nanoseconds => true   // Nanoseconds can use full int range
    }
}

// Main method to create a datetime64 object from integer offset and time unit
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method datetime64(offset: int, unit: TimeUnit) returns (result: DateTime64)
    ensures result.offset == offset
    ensures result.unit == unit
    ensures result.isUtc == true
    ensures ValidDateTime64(result)
// </vc-spec>
// <vc-code>
{
  assume {:axiom} false;
}
// </vc-code>
