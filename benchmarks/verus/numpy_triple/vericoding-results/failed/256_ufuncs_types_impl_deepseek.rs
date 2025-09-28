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
/* helper modified by LLM (iteration 5): replace String operations with a simple character-based approach */
fn build_signature_string(sig: TypeSignature) -> (result_str: String)
    ensures
        result_str@ == format_type_signature(sig)
{
    let mut result = String::new();
    let mut index: usize = 0;
    
    while index < sig.input_types.len()
        invariant
            result@ == sig.input_types@.subrange(0, index as int).map(|i: int, tc: TypeCode| type_code_to_char(tc)),
            index <= sig.input_types.len()
    {
        let tc = sig.input_types[index];
        let c = match tc {
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
        };
        result.push(c);
        index += 1;
    }
    
    result.push('-' as char);
    result.push('>' as char);
    result.push(match sig.output_type {
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
    });
    
    result
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
/* code modified by LLM (iteration 5): use direct string building without intermediate Vec<char> */
{
    let mut result: Vec<String> = Vec::new();
    let mut i: usize = 0;
    
    while i < ufunc_signatures.len()
        invariant
            result.len() == i,
            forall|j: int| 0 <= j < i ==> result[j]@ == format_type_signature(ufunc_signatures[j]),
            i <= ufunc_signatures.len()
    {
        let sig = ufunc_signatures[i];
        let sig_str = build_signature_string(sig);
        result.push(sig_str);
        i += 1;
    }
    
    result
}
// </vc-code>


}
fn main() {}