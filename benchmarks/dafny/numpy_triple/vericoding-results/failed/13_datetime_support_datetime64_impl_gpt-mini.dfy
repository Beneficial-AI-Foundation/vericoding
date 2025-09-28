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
/**
  helper modified by LLM (iteration 5): lemmas for all TimeUnit cases to allow proving ValidDateTime64
*/

/* helper modified by LLM (iteration 5): lemma for Years with required year-range */
lemma ValidForYears(offset: int)
  requires offset + 1970 >= 1 && offset + 1970 <= 9999
  ensures ValidDateTime64(DateTime64(offset, Years, true))
{
}

/* helper modified by LLM (iteration 5): lemma for Days with 32-bit bounds */
lemma ValidForDays(offset: int)
  requires offset >= -2147483648 && offset <= 2147483647
  ensures ValidDateTime64(DateTime64(offset, Days, true))
{
}

/* helper modified by LLM (iteration 5): lemma for Hours with 32-bit bounds */
lemma ValidForHours(offset: int)
  requires offset >= -2147483648 && offset <= 2147483647
  ensures ValidDateTime64(DateTime64(offset, Hours, true))
{
}

/* helper modified by LLM (iteration 5): lemma for Minutes with 32-bit bounds */
lemma ValidForMinutes(offset: int)
  requires offset >= -2147483648 && offset <= 2147483647
  ensures ValidDateTime64(DateTime64(offset, Minutes, true))
{
}

/* helper modified by LLM (iteration 5): lemma for Seconds with 32-bit bounds */
lemma ValidForSeconds(offset: int)
  requires offset >= -2147483648 && offset <= 2147483647
  ensures ValidDateTime64(DateTime64(offset, Seconds, true))
{
}

/* helper modified by LLM (iteration 4): lemmas for always-valid fine-grained units */
lemma ValidForMilliseconds(offset: int)
  ensures ValidDateTime64(DateTime64(offset, Milliseconds, true))
{
}

/* helper modified by LLM (iteration 4): lemmas for always-valid fine-grained units */
lemma ValidForMicroseconds(offset: int)
  ensures ValidDateTime64(DateTime64(offset, Microseconds, true))
{
}

/* helper modified by LLM (iteration 4): lemmas for always-valid fine-grained units */
lemma ValidForNanoseconds(offset: int)
  ensures ValidDateTime64(DateTime64(offset, Nanoseconds, true))
{
}

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
  /* code modified by LLM (iteration 5): construct DateTime64 and call appropriate helper to discharge ValidDateTime64 */
  match unit {
    case Years =>
      // Ensure the offset corresponds to a valid year range before returning
      assert offset + 1970 >= 1 && offset + 1970 <= 9999;
      result := DateTime64(offset, Years, true);
      ValidForYears(offset);
      return;
    case Days =>
      assert offset >= -2147483648 && offset <= 2147483647;
      result := DateTime64(offset, Days, true);
      ValidForDays(offset);
      return;
    case Hours =>
      assert offset >= -2147483648 && offset <= 2147483647;
      result := DateTime64(offset, Hours, true);
      ValidForHours(offset);
      return;
    case Minutes =>
      assert offset >= -2147483648 && offset <= 2147483647;
      result := DateTime64(offset, Minutes, true);
      ValidForMinutes(offset);
      return;
    case Seconds =>
      assert offset >= -2147483648 && offset <= 2147483647;
      result := DateTime64(offset, Seconds, true);
      ValidForSeconds(offset);
      return;
    case Milliseconds =>
      result := DateTime64(offset, Milliseconds, true);
      ValidForMilliseconds(offset);
      return;
    case Microseconds =>
      result := DateTime64(offset, Microseconds, true);
      ValidForMicroseconds(offset);
      return;
    case Nanoseconds =>
      result := DateTime64(offset, Nanoseconds, true);
      ValidForNanoseconds(offset);
      return;
  }
}

// </vc-code>
