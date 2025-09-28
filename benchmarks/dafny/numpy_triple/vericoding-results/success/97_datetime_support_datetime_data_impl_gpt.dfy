// <vc-preamble>
// Datetime unit enumeration representing the time scales used in datetime operations
datatype DatetimeUnit = 
  | Y    // Years
  | M    // Months  
  | W    // Weeks
  | D    // Days
  | h    // Hours
  | m    // Minutes
  | s    // Seconds
  | ms   // Milliseconds
  | us   // Microseconds
  | ns   // Nanoseconds

// Structure containing datetime type information including unit and count
datatype DatetimeTypeInfo = DatetimeTypeInfo(
  unit: DatetimeUnit,   // The time unit (seconds, minutes, hours, etc.)
  count: nat            // The count of base units in a step (e.g., 25 for "25 seconds")
)

// Datetime dtype representing either datetime64 or timedelta64 types  
datatype DatetimeDtype =
  | datetime64(info: DatetimeTypeInfo)   // A datetime64 type with specified unit and count
  | timedelta64(info: DatetimeTypeInfo)  // A timedelta64 type with specified unit and count

// Get information about the step size of a date or time type
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): getters for DatetimeTypeInfo fields to simplify access */
function getUnit(info: DatetimeTypeInfo): DatetimeUnit {
  info.unit
}

/* helper modified by LLM (iteration 2): getter for count with non-negativity ensured by type nat */
function getCount(info: DatetimeTypeInfo): nat {
  info.count
}
// </vc-helpers>

// <vc-spec>
method datetime_data(dtype: DatetimeDtype) returns (unit: DatetimeUnit, count: nat)
  requires dtype.datetime64? ==> dtype.info.count > 0
  requires dtype.timedelta64? ==> dtype.info.count > 0
  ensures unit == dtype.info.unit
  ensures count == dtype.info.count
  ensures count > 0
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 2): fixed match syntax and return values for both datetime64 and timedelta64 */
  match dtype {
    case datetime64(info) =>
      unit := info.unit;
      count := info.count;
    case timedelta64(info) =>
      unit := info.unit;
      count := info.count;
  }
}
// </vc-code>
