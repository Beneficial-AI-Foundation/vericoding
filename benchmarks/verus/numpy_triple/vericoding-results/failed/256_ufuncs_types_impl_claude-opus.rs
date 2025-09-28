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
{
    /* code modified by LLM (iteration 5): Fix type error by dereferencing sig */
    let mut result: Vec<String> = Vec::new();
    let mut i = 0;
    while i < ufunc_signatures.len()
        invariant
            0 <= i <= ufunc_signatures.len(),
            result.len() == i,
            forall|j: int| 0 <= j < i ==> result[j]@ == format_type_signature(ufunc_signatures[j]),
            forall|j: int| 0 <= j < ufunc_signatures.len() ==> ufunc_signatures[j].input_types.len() > 0
    {
        let sig = &ufunc_signatures[i];
        
        // Build character sequence
        let mut chars: Vec<char> = Vec::new();
        
        // Add input type characters
        let mut j = 0;
        while j < sig.input_types.len()
            invariant
                0 <= j <= sig.input_types.len(),
                chars@.len() == j,
                forall|k: int| 0 <= k < j ==> chars@[k] == type_code_to_char(sig.input_types@[k])
        {
            let tc = sig.input_types[j];
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
            chars.push(c);
            j = j + 1;
        }
        
        // Add arrow
        chars.push('-');
        chars.push('>');
        
        // Add output type character
        let out_c = match sig.output_type {
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
        chars.push(out_c);
        
        // Create string from chars
        let s = String::from_utf8(chars.into_iter().map(|c| c as u8).collect()).unwrap();
        
        assert(s@ == format_type_signature(ufunc_signatures[i]));
        result.push(s);
        i = i + 1;
    }
    result
}
// </vc-code>


}
fn main() {}