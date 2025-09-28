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
/* helper modified by LLM (iteration 2): Added helper function to create old print options for context manager */ function createOldOptions(new_opts: PrintOptions): PrintOptions { if new_opts.precision > 0 then PrintOptions(0, new_opts.threshold, new_opts.edgeitems, new_opts.linewidth, new_opts.suppress, new_opts.nanstr, new_opts.infstr) else PrintOptions(1, new_opts.threshold, new_opts.edgeitems, new_opts.linewidth, new_opts.suppress, new_opts.nanstr, new_opts.infstr) }
// </vc-helpers>

// <vc-spec>
method numpy_printoptions(new_opts: PrintOptions) returns (context: PrintOptionsContext)
  requires true  // Valid print options are provided (always satisfied for well-formed PrintOptions)
  ensures context.new_options == new_opts  // New options match the input
  ensures context.old_options != context.new_options  // Options are actually changed
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 2): Implemented numpy_printoptions by creating old options and returning context, using renamed variable to avoid keyword conflict */ {
  var original := createOldOptions(new_opts);
  context := PrintOptionsContext(original, new_opts);
}
// </vc-code>
