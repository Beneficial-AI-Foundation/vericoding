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
/* helper modified by LLM (iteration 3): construct PrintOptions from fields */
fn make_printoptions(precision: usize, threshold: usize, edgeitems: usize, linewidth: usize, suppress: bool, nanstr: String, infstr: String) -> PrintOptions {
    PrintOptions {
        precision: precision,
        threshold: threshold,
        edgeitems: edgeitems,
        linewidth: linewidth,
        suppress: suppress,
        nanstr: nanstr,
        infstr: infstr,
    }
}
// </vc-helpers>

// <vc-spec>
fn numpy_printoptions(new_opts: PrintOptions) -> (context: PrintOptionsContext)
    ensures 
        context.new_options == new_opts,
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 3): clone string fields and build context without using String::new */
    let nan_clone = new_opts.nanstr.clone();
    let inf_clone = new_opts.infstr.clone();
    let old = make_printoptions(new_opts.precision, new_opts.threshold, new_opts.edgeitems, new_opts.linewidth, new_opts.suppress, nan_clone, inf_clone);
    let ctx: PrintOptionsContext = PrintOptionsContext {
        old_options: old,
        new_options: new_opts,
    };
    ctx
}
// </vc-code>


}
fn main() {}