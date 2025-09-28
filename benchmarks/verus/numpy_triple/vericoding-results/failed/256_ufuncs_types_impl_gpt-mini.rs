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
/* helper modified by LLM (iteration 5): convert Seq<char> to String by pushing chars */
fn seq_to_string(s: Seq<char>) -> (result: String)
    ensures
        result@ == s,
{
    let mut res = String::new();
    let mut i: usize = 0;
    while i < s.len()
        invariant
            i <= s.len(),
            res.len() == i,
            forall|k: int| 0 <= k < res.len() ==>
                res@@[k] == s@[k],
        decreases s.len() - i,
    {
        let idx: int = i as int;
        let c: char = s@[idx];
        res.push(c);
        i += 1;
    }
    proof {
        assert(res.len() == s.len());
        assert(forall|k: int| 0 <= k < res.len() ==> res@@[k] == s@[k]);
    }
    res
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
/* code modified by LLM (iteration 5): build strings for each TypeSignature */
{
    let mut result: Vec<String> = Vec::new();
    let mut j: usize = 0;
    while j < ufunc_signatures.len()
        invariant
            j <= ufunc_signatures.len(),
            result.len() == j,
            forall|k: int| 0 <= k < result.len() ==>
                result[k]@ == format_type_signature(ufunc_signatures[k]) &&
                ufunc_signatures[k].input_types.len() > 0,
        decreases ufunc_signatures.len() - j,
    {
        let sig = ufunc_signatures[j];
        let seq = format_type_signature(sig);
        let s = seq_to_string(seq);
        result.push(s);
        j += 1;
    }
    result
}

// </vc-code>


}
fn main() {}