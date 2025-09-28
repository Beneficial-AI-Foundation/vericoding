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
fn type_code_to_char_exec(tc: TypeCode) -> (c: char)
    ensures c == type_code_to_char(tc)
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

/* helper modified by LLM (iteration 5): [Replaced Vec<char> and collect() with direct String manipulation to fix compilation error.] */
fn format_one_signature_exec(sig: &TypeSignature) -> (result: String)
    ensures result@ == format_type_signature(*sig),
{
    let mut result_str = String::new();
    let mut i: usize = 0;
    while i < sig.input_types.len()
        invariant
            i <= sig.input_types.len(),
            result_str@ == sig.input_types@.subrange(0, i as int).map(|_idx: int, tc: TypeCode| type_code_to_char(tc)),
        decreases sig.input_types.len() - i
    {
        let tc = sig.input_types[i];
        let c = type_code_to_char_exec(tc);
        result_str.push(c);
        i = i + 1;
    }

    result_str.push('-');
    result_str.push('>');

    let out_char = type_code_to_char_exec(sig.output_type);
    result_str.push(out_char);
    
    result_str
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
{
    /* code modified by LLM (iteration 5): [No logical changes; the compilation error was in a helper function.] */
    let mut results: Vec<String> = Vec::new();
    let mut i: usize = 0;
    while i < ufunc_signatures.len()
        invariant
            i <= ufunc_signatures.len(),
            results.len() == i,
            forall|j: int| 0 <= j < i ==> results[j]@ == format_type_signature(ufunc_signatures[j]),
            forall|j: int| 0 <= j < i ==> ufunc_signatures[j].input_types.len() > 0,
        decreases ufunc_signatures.len() - i
    {
        let sig = &ufunc_signatures[i];
        assert(sig.input_types.len() > 0);
        let s = format_one_signature_exec(sig);
        results.push(s);
        i = i + 1;
    }
    results
}
// </vc-code>


}
fn main() {}