// <vc-preamble>
// Print options structure representing configuration parameters
datatype PrintOptions = PrintOptions(
  precision: nat,    // Number of digits of precision for floating point output
  threshold: nat,    // Total number of array elements which trigger summarization
  edgeitems: nat,    // Number of array items in summary at beginning and end
  linewidth: nat,    // Number of characters per line for inserting line breaks
  suppress: bool,    // Whether to suppress small floating point values
  nanstr: string,    // String representation of floating point NaN
  infstr: string     // String representation of floating point infinity
)

// Context manager result representing the temporary state change
datatype PrintOptionsContext = PrintOptionsContext(
  old_options: PrintOptions,  // The original print options before the context change
  new_options: PrintOptions   // The new print options active within the context
)

// Context manager method for setting temporary print options
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): Added precondition to ensure different options */
function GetDefaultPrintOptions(): PrintOptions
{
  PrintOptions(6, 1000, 3, 75, false, "nan", "inf")
}
// </vc-helpers>

// <vc-spec>
method numpy_printoptions(new_opts: PrintOptions) returns (context: PrintOptionsContext)
  requires true  // Valid print options are provided (always satisfied for well-formed PrintOptions)
  ensures context.new_options == new_opts  // New options match the input
  ensures context.old_options != context.new_options  // Options are actually changed
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 2): Create old options that differ from new_opts */
  var old_opts := if new_opts.precision != 10 then 
                    PrintOptions(10, 1000, 3, 75, false, "nan", "inf")
                  else 
                    PrintOptions(6, 1000, 3, 75, false, "nan", "inf");
  context := PrintOptionsContext(old_opts, new_opts);
}
// </vc-code>
