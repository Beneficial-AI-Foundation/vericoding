// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
/* Structure representing NumPy print options */
struct PrintOptions {
    /* Number of digits of precision for floating point output */
    precision: u8,
    /* Total number of array elements which trigger summarization */
    threshold: u8,
    /* Number of array items in summary at beginning and end */
    edgeitems: u8,
    /* Number of characters per line for line breaks */
    linewidth: u8,
    /* Whether to suppress small floating point values */
    suppress: bool,
    /* String representation of floating point not-a-number */
    nanstr: Vec<char>,
    /* String representation of floating point infinity */
    infstr: Vec<char>,
    /* Controls printing of the sign of floating-point types */
    sign: Vec<char>,
    /* Controls interpretation of precision option */
    floatmode: Vec<char>,
    /* Legacy printing mode setting */
    legacy: Option<Vec<char>>,
}

fn get_printoptions() -> (result: PrintOptions)
    ensures
        result.precision as nat > 0,
        result.threshold as nat > 0,
        result.edgeitems as nat > 0,
        result.linewidth as nat > 0,
        result.nanstr@.len() > 0,
        result.infstr@.len() > 0,
        (result.sign@ == seq!['-'] || result.sign@ == seq!['+'] || result.sign@ == seq![' ']),
        (result.floatmode@ == seq!['f','i','x','e','d'] ||
         result.floatmode@ == seq!['u','n','i','q','u','e'] ||
         result.floatmode@ == seq!['m','a','x','p','r','e','c'] ||
         result.floatmode@ == seq!['m','a','x','p','r','e','c','_','e','q','u','a','l'])
// </vc-spec>
// <vc-code>
{
    let precision: u8 = 8;
    let threshold: u8 = 100;
    let edgeitems: u8 = 3;
    let linewidth: u8 = 75;
    let suppress: bool = false;
    let nanstr: Vec<char> = vec!['n', 'a', 'n'];
    let infstr: Vec<char> = vec!['i', 'n', 'f'];
    let sign: Vec<char> = vec!['-'];
    let floatmode: Vec<char> = vec!['f', 'i', 'x', 'e', 'd'];
    let legacy: Option<Vec<char>> = None;
    
    let result = PrintOptions {
        precision,
        threshold,
        edgeitems,
        linewidth,
        suppress,
        nanstr,
        infstr,
        sign,
        floatmode,
        legacy,
    };
    
    result
}
// </vc-code>


}
fn main() {}