/* List of supported data type signatures for universal functions.
Shows input->output type mappings.
Example: add.types: ['??->?', 'bb->b', 'BB->B', 'hh->h', ...]

Returns the list of supported data type signatures for a universal function.

Specification: types returns formatted type signatures as strings. */

use vstd::prelude::*;

verus! {

/* Data type character codes used in NumPy ufunc type signatures */
#[derive(PartialEq, Eq, Clone, Copy)]
enum TypeCode {
    Bool,     /* '?' */
    Byte,     /* 'b' */
    Ubyte,    /* 'B' */
    Short,    /* 'h' */
    Ushort,   /* 'H' */
    Int,      /* 'i' */
    Uint,     /* 'I' */
    Long,     /* 'l' */
    Ulong,    /* 'L' */
    Longlong, /* 'q' */
    Ulonglong,/* 'Q' */
    Float32,  /* 'f' */
    Float64,  /* 'd' */
    Longdouble, /* 'g' */
    Complex64,/* 'F' */
    Complex128,/* 'D' */
    Clongdouble,/* 'G' */
    Object,   /* 'O' */
}

/* Type signature representing input->output mapping for ufuncs */
#[derive(Clone)]
struct TypeSignature {
    input_types: Vec<TypeCode>,
    output_type: TypeCode,
}

/* Convert TypeCode to character representation */
spec fn type_code_to_char(tc: TypeCode) -> char {
    match tc {
        TypeCode::Bool => '?',
        TypeCode::Byte => 'b',
        TypeCode::Ubyte => 'B',
        TypeCode::Short => 'h',
        TypeCode::Ushort => 'H',
        TypeCode::Int => 'i',
        TypeCode::Uint => 'I',
        TypeCode::Long => 'l',
        TypeCode::Ulong => 'L',
        TypeCode::Longlong => 'q',
        TypeCode::Ulonglong => 'Q',
        TypeCode::Float32 => 'f',
        TypeCode::Float64 => 'd',
        TypeCode::Longdouble => 'g',
        TypeCode::Complex64 => 'F',
        TypeCode::Complex128 => 'D',
        TypeCode::Clongdouble => 'G',
        TypeCode::Object => 'O',
    }
}

/* Format a type signature as a string (input1input2...->output) */
spec fn format_type_signature(sig: TypeSignature) -> Seq<char> {
    let input_chars = sig.input_types@.map(|i, tc: TypeCode| type_code_to_char(tc));
    let arrow_chars = seq!['-', '>'];
    let output_char = seq![type_code_to_char(sig.output_type)];
    input_chars + arrow_chars + output_char
}
fn types(ufunc_signatures: Vec<TypeSignature>) -> (result: Vec<Vec<char>>)
    requires ufunc_signatures.len() >= 0,
    ensures 
        result.len() == ufunc_signatures.len(),
        forall|i: int| 0 <= i < result.len() ==> 
            result[i]@ == format_type_signature(ufunc_signatures[i]) &&
            ufunc_signatures[i].input_types.len() > 0,
{
    // impl-start
    assume(false);
    Vec::new()
    // impl-end
}
}
fn main() {}