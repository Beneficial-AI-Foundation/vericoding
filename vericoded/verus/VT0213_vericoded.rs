// <vc-preamble>
use vstd::prelude::*;

verus! {

/* Print options structure to represent configuration */
struct PrintOptions {
    /* Number of digits of precision for floating point output */
    precision: usize,
    /* Total number of array elements which trigger summarization */
    threshold: usize,
    /* Number of array items in summary at beginning and end */
    edgeitems: usize,
    /* Number of characters per line for inserting line breaks */
    linewidth: usize,
    /* Whether to suppress small floating point values */
    suppress: bool,
    /* String representation of floating point NaN */
    nanstr: String,
    /* String representation of floating point infinity */
    infstr: String,
}

/* Context manager result representing the temporary state change */
struct PrintOptionsContext {
    /* The original print options before the context change */
    old_options: PrintOptions,
    /* The new print options active within the context */
    new_options: PrintOptions,
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): provide external-body constructor for default print options avoiding unsupported String::new in verified context */
#[verifier(external_body)]
fn default_print_options() -> (opts: PrintOptions)
    ensures
        opts.precision == 0usize,
        opts.threshold == 0usize,
        opts.edgeitems == 0usize,
        opts.linewidth == 0usize,
        opts.suppress == false,
{
    let ns = String::new();
    let is = String::new();
    let opts_res = PrintOptions {
        precision: 0usize,
        threshold: 0usize,
        edgeitems: 0usize,
        linewidth: 0usize,
        suppress: false,
        nanstr: ns,
        infstr: is,
    };
    opts_res
}
// </vc-helpers>

// <vc-spec>
fn numpy_printoptions(new_opts: PrintOptions) -> (context: PrintOptionsContext)
    ensures 
        context.new_options == new_opts,
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): construct context using provided new options and default old options */
    let old_options = default_print_options();
    let context = PrintOptionsContext {
        old_options,
        new_options: new_opts,
    };
    context
}
// </vc-code>


}
fn main() {}