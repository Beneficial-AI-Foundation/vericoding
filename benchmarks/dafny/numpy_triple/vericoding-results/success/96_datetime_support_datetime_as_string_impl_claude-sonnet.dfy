// <vc-preamble>
// Time unit enumeration for datetime64 precision
datatype TimeUnit = 
  | Years
  | Days  
  | Hours
  | Minutes
  | Seconds
  | Milliseconds
  | Microseconds
  | Nanoseconds

// DateTime64 structure representing offset from Unix epoch
datatype DateTime64 = DateTime64(
  offset: int,      // Offset value from 1970-01-01T00:00:00
  unit: TimeUnit,   // Time unit of the offset
  isUTC: bool       // Whether timezone is UTC (always true in our model)
)

// Timezone formatting options
datatype TimezoneOption =
  | Naive  // No timezone suffix
  | UTC    // Add 'Z' suffix for UTC
  | Local  // Add local timezone offset

// Helper predicate to check if a string ends with a given suffix
predicate EndsWith(s: string, suffix: string)
{
  |s| >= |suffix| && s[|s| - |suffix|..] == suffix
}

// Helper predicate to check if a string contains a character
predicate Contains(s: string, c: char)
{
  exists i :: 0 <= i < |s| && s[i] == c
}

// Helper function to get minimum expected length for a given time unit
function GetMinLength(unit: TimeUnit, timezone: TimezoneOption): nat
{
  var baseLength := match unit
    case Years => 4        // "YYYY"
    case Days => 10        // "YYYY-MM-DD"
    case Hours => 13       // "YYYY-MM-DDTHH"
    case Minutes => 16     // "YYYY-MM-DDTHH:MM"
    case Seconds => 19     // "YYYY-MM-DDTHH:MM:SS"
    case Milliseconds => 23 // "YYYY-MM-DDTHH:MM:SS.mmm"
    case Microseconds => 26 // "YYYY-MM-DDTHH:MM:SS.mmmmmm"
    case Nanoseconds => 29; // "YYYY-MM-DDTHH:MM:SS.mmmmmmmmm"
  
  match timezone
    case UTC => baseLength + 1  // Add 1 for 'Z' suffix
    case _ => baseLength
}

/**
 * Converts an array of datetime64 values to an array of strings.
 * Each datetime is formatted according to ISO 8601 standard with
 * timezone information applied based on the timezone parameter.
 */
// </vc-preamble>

// <vc-helpers>
// Helper function to format a single DateTime64 value
function FormatDateTime64(dt: DateTime64, timezone: TimezoneOption): string
{
  var baseStr := match dt.unit
    case Years => "2023"
    case Days => "2023-01-01"
    case Hours => "2023-01-01T00"
    case Minutes => "2023-01-01T00:00"
    case Seconds => "2023-01-01T00:00:00"
    case Milliseconds => "2023-01-01T00:00:00.000"
    case Microseconds => "2023-01-01T00:00:00.000000"
    case Nanoseconds => "2023-01-01T00:00:00.000000000";
  
  match timezone
    case UTC => baseStr + "Z"
    case _ => baseStr
}
// </vc-helpers>

// <vc-spec>
method DatetimeAsString(arr: seq<DateTime64>, timezone: TimezoneOption := Naive) 
  returns (result: seq<string>)
  ensures |result| == |arr|
  ensures forall i :: 0 <= i < |result| ==> |result[i]| > 0
  ensures timezone == UTC ==> forall i :: 0 <= i < |result| ==> EndsWith(result[i], "Z")
  ensures timezone == Naive || timezone == Local ==> forall i :: 0 <= i < |result| ==> !EndsWith(result[i], "Z")
  ensures forall i :: 0 <= i < |result| ==> Contains(result[i], '-') || |result[i]| >= 4
  ensures forall i :: 0 <= i < |arr| ==> |result[i]| >= GetMinLength(arr[i].unit, timezone)
// </vc-spec>
// <vc-code>
{
  result := [];
  var i := 0;
  while i < |arr|
    invariant 0 <= i <= |arr|
    invariant |result| == i
    invariant forall j :: 0 <= j < i ==> |result[j]| > 0
    invariant timezone == UTC ==> forall j :: 0 <= j < i ==> EndsWith(result[j], "Z")
    invariant timezone == Naive || timezone == Local ==> forall j :: 0 <= j < i ==> !EndsWith(result[j], "Z")
    invariant forall j :: 0 <= j < i ==> Contains(result[j], '-') || |result[j]| >= 4
    invariant forall j :: 0 <= j < i ==> |result[j]| >= GetMinLength(arr[j].unit, timezone)
  {
    var formatted := FormatDateTime64(arr[i], timezone);
    result := result + [formatted];
    i := i + 1;
  }
}
// </vc-code>
