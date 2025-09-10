use vstd::prelude::*;

verus! {

#[derive(PartialEq, Eq, Structural)]
enum TypeCode {
    Bool,
    Byte,
    UByte,
    Short,
    UShort,
    Int,
    UInt,
    Long,
    ULong,
    LongLong,
    ULongLong,
    Float32,
    Float64,
    LongDouble,
    Complex64,
    Complex128,
    CLongDouble,
    Object,
}

struct TypeSignature {
    input_types: Vec<TypeCode>,
    output_type: TypeCode,
}

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

spec fn format_type_signature(sig: TypeSignature) -> Seq<char> {
    let input_chars = sig.input_types@.map(|i, tc: TypeCode| type_code_to_char(tc));
    input_chars + seq!['-', '>'] + seq![type_code_to_char(sig.output_type)]
}

fn types(ufunc_signatures: Vec<TypeSignature>) -> (result: Vec<String>)
    ensures 
        result.len() == ufunc_signatures.len(),
        forall|i: int| 0 <= i < result.len() ==> {
            let sig = ufunc_signatures[i];
            sig.input_types.len() > 0 &&
            result[i]@ == format_type_signature(sig)
        }
{
    assume(false);
    unreached();
}

}
fn main() {}