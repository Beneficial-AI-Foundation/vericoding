// <vc-preamble>
use vstd::prelude::*;

verus! {

/* Structure representing NumPy print options */
struct PrintOptions {
    /* Number of digits of precision for floating point output */
    precision: nat,
    /* Total number of array elements which trigger summarization */
    threshold: nat,
    /* Number of array items in summary at beginning and end */
    edgeitems: nat,
    /* Number of characters per line for line breaks */
    linewidth: nat,
    /* Whether to suppress small floating point values */
    suppress: bool,
    /* String representation of floating point not-a-number */
    nanstr: String,
    /* String representation of floating point infinity */
    infstr: String,
    /* Controls printing of the sign of floating-point types */
    sign: String,
    /* Controls interpretation of precision option */
    floatmode: String,
    /* Legacy printing mode setting */
    legacy: Option<String>,
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): make helper visible (pub open) and keep simple validation */
pub open spec fn valid_sign(s: Seq<char>) -> bool { s.len() == 1 && (s == seq!['-'] || s == seq!['+'] || s == seq![' ']) }

/* helper modified by LLM (iteration 2): expose floatmode validator */
pub open spec fn valid_floatmode(s: Seq<char>) -> bool {
    s == seq!['f','i','x','e','d'] ||
    s == seq!['u','n','i','q','u','e'] ||
    s == seq!['m','a','x','p','r','e','c'] ||
    s == seq!['m','a','x','p','r','e','c','_','e','q','u','a','l']
}

/* helper modified by LLM (iteration 2): expose legacy validator */
pub open spec fn valid_legacy(s: Seq<char>) -> bool {
    s == seq!['1','.','1','3'] ||
    s == seq!['1','.','2','1'] ||
    s == seq!['1','.','2','5'] ||
    s == seq!['2','.','1'] ||
    s == seq!['2','.','2']
}
// </vc-helpers>

// <vc-spec>
fn set_printoptions(
    precision: Option<u8>,
    threshold: Option<u8>,
    edgeitems: Option<u8>,
    linewidth: Option<u8>,
    suppress: Option<bool>,
    nanstr: Option<String>,
    infstr: Option<String>,
    sign: Option<String>,
    floatmode: Option<String>,
    legacy: Option<String>
) -> (result: ())
    requires
        forall|p: u8| precision == Some(p) ==> p as nat > 0,
        forall|t: u8| threshold == Some(t) ==> t as nat > 0,
        forall|e: u8| edgeitems == Some(e) ==> e as nat > 0,
        forall|l: u8| linewidth == Some(l) ==> l as nat > 0,
        forall|n: String| nanstr == Some(n) ==> n@.len() > 0,
        forall|i: String| infstr == Some(i) ==> i@.len() > 0,
        forall|s: String| sign == Some(s) ==> (s@.len() == 1 && (s@ == seq!['-'] || s@ == seq!['+'] || s@ == seq![' '])),
        forall|f: String| floatmode == Some(f) ==> 
            (f@ == seq!['f','i','x','e','d'] || f@ == seq!['u','n','i','q','u','e'] || f@ == seq!['m','a','x','p','r','e','c'] || f@ == seq!['m','a','x','p','r','e','c','_','e','q','u','a','l']),
        forall|l: String| legacy == Some(l) ==> 
            (l@ == seq!['1','.','1','3'] || l@ == seq!['1','.','2','1'] || l@ == seq!['1','.','2','5'] || l@ == seq!['2','.','1'] || l@ == seq!['2','.','2']),
    ensures result == ()
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): trivial body returning unit and referencing inputs to avoid unused warnings */
    let _ = precision;
    let _ = threshold;
    let _ = edgeitems;
    let _ = linewidth;
    let _ = suppress;
    let _ = nanstr;
    let _ = infstr;
    let _ = sign;
    let _ = floatmode;
    let _ = legacy;
    ()
}
// </vc-code>


}
fn main() {}