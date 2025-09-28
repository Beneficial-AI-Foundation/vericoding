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
/* helper modified by LLM (iteration 4): validate sign string */
spec fn valid_sign(s: &String) -> bool {
    s@.len() == 1 && (s@ == seq!['-'] || s@ == seq!['+'] || s@ == seq![' '])
}

/* helper modified by LLM (iteration 4): validate floatmode string */
spec fn valid_floatmode(f: &String) -> bool {
    let v = f@;
    v == seq!['f','i','x','e','d'] || v == seq!['u','n','i','q','u','e'] || v == seq!['m','a','x','p','r','e','c'] || v == seq!['m','a','x','p','r','e','c','_','e','q','u','a','l']
}

/* helper modified by LLM (iteration 4): validate legacy string */
spec fn valid_legacy(l: &String) -> bool {
    let v = l@;
    v == seq!['1','.','1','3'] || v == seq!['1','.','2','1'] || v == seq!['1','.','2','5'] || v == seq!['2','.','1'] || v == seq!['2','.','2']
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
    /* code modified by LLM (iteration 4): validate inputs in a proof block and return unit */
    proof {
        match precision { Some(p) => { assert(p as nat > 0); }, None => {} }
        match threshold { Some(t) => { assert(t as nat > 0); }, None => {} }
        match edgeitems { Some(e) => { assert(e as nat > 0); }, None => {} }
        match linewidth { Some(l) => { assert(l as nat > 0); }, None => {} }
        match nanstr { Some(ref s) => { assert(s@.len() > (0 as nat)); }, None => {} }
        match infstr { Some(ref s) => { assert(s@.len() > (0 as nat)); }, None => {} }
        match sign { Some(ref s) => { assert(valid_sign(s)); }, None => {} }
        match floatmode { Some(ref s) => { assert(valid_floatmode(s)); }, None => {} }
        match legacy { Some(ref s) => { assert(valid_legacy(s)); }, None => {} }
    }

    ()
}
// </vc-code>


}
fn main() {}