// <vc-preamble>
use vstd::prelude::*;

verus! {
/* Data type character codes used in NumPy ufunc type signatures */
#[derive(PartialEq, Eq)]
enum TypeCode {
    Bool,       // '?'
    Byte,       // 'b' 
    UByte,      // 'B'
    Short,      // 'h'
    UShort,     // 'H'
    Int,        // 'i'
    UInt,       // 'I'
    Long,       // 'l'
    ULong,      // 'L'
    LongLong,   // 'q'
    ULongLong,  // 'Q'
    Float32,    // 'f'
    Float64,    // 'd'
    LongDouble, // 'g'
    Complex64,  // 'F'
    Complex128, // 'D'
    CLongDouble,// 'G'
    Object,     // 'O'
}

/* Type signature representing input->output mapping for ufuncs */
struct TypeSignature {
    input_types: Vec<TypeCode>,
    output_type: TypeCode,
}

/* Convert TypeCode to character representation */
spec fn type_code_to_char(tc: TypeCode) -> char {
    match tc {
        TypeCode::Bool => '?',
        TypeCode::Byte => 'b',
        TypeCode::UByte => 'B',
        TypeCode::Short => 'h',
        TypeCode::UShort => 'H',
        TypeCode::Int => 'i',
        TypeCode::UInt => 'I',
        TypeCode::Long => 'l',
        TypeCode::ULong => 'L',
        TypeCode::LongLong => 'q',
        TypeCode::ULongLong => 'Q',
        TypeCode::Float32 => 'f',
        TypeCode::Float64 => 'd',
        TypeCode::LongDouble => 'g',
        TypeCode::Complex64 => 'F',
        TypeCode::Complex128 => 'D',
        TypeCode::CLongDouble => 'G',
        TypeCode::Object => 'O',
    }
}

/* Format a type signature as a string (input1input2...->output) */
spec fn format_type_signature(sig: TypeSignature) -> Seq<char> {
    let input_chars = sig.input_types@.map(|i: int, tc: TypeCode| type_code_to_char(tc));
    let arrow_chars = seq!['-', '>'];
    let output_char = seq![type_code_to_char(sig.output_type)];
    input_chars + arrow_chars + output_char
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): removed local variable to avoid shadowing */
exec fn type_code_to_char_exec(tc: TypeCode) -> char
    ensures
        result == type_code_to_char(tc)
{
    match tc {
        TypeCode::Bool => '?',
        TypeCode::Byte => 'b',
        TypeCode::UByte => 'B',
        TypeCode::Short => 'h',
        TypeCode::UShort => 'H',
        TypeCode::Int => 'i',
        TypeCode::UInt => 'I',
        TypeCode::Long => 'l',
        TypeCode::ULong => 'L',
        TypeCode::LongLong => 'q',
        TypeCode::ULongLong => 'Q',
        TypeCode::Float32 => 'f',
        TypeCode::Float64 => 'd',
        TypeCode::LongDouble => 'g',
        TypeCode::Complex64 => 'F',
        TypeCode::Complex128 => 'D',
        TypeCode::CLongDouble => 'G',
        TypeCode::Object => 'O',
    }
}

/* helper modified by LLM (iteration 5): renamed local variable to avoid shadowing */
exec fn format_type_signature_exec(sig: &TypeSignature) -> String
    requires
        sig.input_types.len() > 0,
    ensures
        result@ == format_type_signature(*sig)
{
    let mut s = String::new();
    for i in 0..sig.input_types.len()
        invariant
            s@ == sig.input_types@.subrange(0, i as int).map(|j: int, tc: TypeCode| type_code_to_char(tc)),
    {
        let tc = sig.input_types[i];
        let c = type_code_to_char_exec(tc);
        s.push(c);
    }
    s.push('-');
    s.push('>');
    let out_c = type_code_to_char_exec(sig.output_type);
    s.push(out_c);
    s
}
// </vc-helpers>

// <vc-spec>
fn types(ufunc_signatures: Vec<TypeSignature>) -> (result: Vec<String>)
    ensures
        result.len() == ufunc_signatures.len(),
        forall|i: int| 0 <= i < result.len() ==>
            result[i]@ == format_type_signature(ufunc_signatures[i]) &&
            ufunc_signatures[i].input_types.len() > 0
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): no changes needed */
{
    for i in 0..ufunc_signatures.len() {
        if ufunc_signatures[i].input_types.len() == 0 {
            panic!("Input type signature must have at least one input type");
        }
    }
    let mut result = Vec::new();
    for sig in ufunc_signatures {
        let formatted = format_type_signature_exec(&sig);
        result.push(formatted);
    }
    result
}
// </vc-code>


}
fn main() {}