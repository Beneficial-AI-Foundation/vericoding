// <vc-preamble>
// Datatype representing an optional string value
datatype OptionalString = None | Some(value: string)

// Datatype representing NumPy print options configuration
datatype PrintOptions = PrintOptions(
  // Number of digits of precision for floating point output
  precision: nat,
  // Total number of array elements which trigger summarization  
  threshold: nat,
  // Number of array items in summary at beginning and end
  edgeitems: nat,
  // Number of characters per line for line breaks
  linewidth: nat,
  // Whether to suppress small floating point values
  suppress: bool,
  // String representation of floating point not-a-number
  nanstr: string,
  // String representation of floating point infinity
  infstr: string,
  // Controls printing of the sign of floating-point types
  sign: string,
  // Controls interpretation of precision option
  floatmode: string,
  // Legacy printing mode setting (None if not set)
  legacy: OptionalString
)

// Predicate to validate that a PrintOptions instance has sensible values
predicate ValidPrintOptions(opts: PrintOptions)
{
  && opts.precision > 0
  && opts.threshold > 0  
  && opts.edgeitems > 0
  && opts.linewidth > 0
  && |opts.nanstr| > 0
  && |opts.infstr| > 0
  && (opts.sign == "-" || opts.sign == "+" || opts.sign == " ")
  && (opts.floatmode == "fixed" || opts.floatmode == "unique" || 
      opts.floatmode == "maxprec" || opts.floatmode == "maxprec_equal")
}

// Method to retrieve current NumPy print options
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method GetPrintOptions() returns (result: PrintOptions)
  // No preconditions - can always query current print options
  ensures ValidPrintOptions(result)
  // Ensures the returned options represent a valid configuration state
// </vc-spec>
// <vc-code>
{
  result := PrintOptions(
    precision := 8,
    threshold := 1000,
    edgeitems := 3,
    linewidth := 75,
    suppress := false,
    nanstr := "nan",
    infstr := "inf",
    sign := "-",
    floatmode := "maxprec",
    legacy := None
  );
}
// </vc-code>
