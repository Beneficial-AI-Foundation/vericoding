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
/* helper modified by LLM (iteration 2): function to create default print options */
function DefaultPrintOptions(): PrintOptions
{
  PrintOptions(10, 1000, 3, 75, false, "nan", "inf")
}

/* helper modified by LLM (iteration 2): predicate to check if two print options are different */
predicate PrintOptionsDifferent(opts1: PrintOptions, opts2: PrintOptions)
{
  opts1.precision != opts2.precision ||
  opts1.threshold != opts2.threshold ||
  opts1.edgeitems != opts2.edgeitems ||
  opts1.linewidth != opts2.linewidth ||
  opts1.suppress != opts2.suppress ||
  opts1.nanstr != opts2.nanstr ||
  opts1.infstr != opts2.infstr
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
  /* code modified by LLM (iteration 2): ensure old options differ from new options */
  var old_opts := DefaultPrintOptions();
  
  if old_opts == new_opts {
    // If new_opts matches default, create a different old_opts
    old_opts := PrintOptions(old_opts.precision + 1, old_opts.threshold, old_opts.edgeitems, old_opts.linewidth, old_opts.suppress, old_opts.nanstr, old_opts.infstr);
  }
  
  context := PrintOptionsContext(old_opts, new_opts);
}
// </vc-code>
