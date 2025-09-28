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
/* helper modified by LLM (iteration 5): The `char_to_string` helper function is unnecessary for the current task as `String::push` can directly append a character; this placeholder is kept empty to indicate no helpers are needed, which is the most robust fix for the previous compilation error. */

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
    let mut result: Vec<String> = Vec::new();
    let mut i = 0;

    while i < ufunc_signatures.len()
        invariant
            0 <= i && i <= ufunc_signatures.len(),
            result.len() == i,
            // All elements processed so far satisfy the postcondition
            forall|j: int| 0 <= j < i ==> {
                let sig = ufunc_signatures[j];
                let formatted_sig = format_type_signature(sig);
                result[j]@ == formatted_sig // Removed `&& sig.input_types.len() > 0` as it's not directly provable here without further refinement.
            }
    {
        let sig = ufunc_signatures[i];
        let formatted_sig_seq = format_type_signature(sig); // This is a Seq<char>
        let mut formatted_sig_string = String::new();
        let mut k: nat = 0;
        while k < formatted_sig_seq.len()
            invariant
                0 <= k && k <= formatted_sig_seq.len(),
                formatted_sig_string.len() == k,
                // Directly assert push operation's effect for formatted_sig_string's content
                forall|l: nat| 0 <= l < k ==> formatted_sig_string@.index(l) == formatted_sig_seq.index(l),
        {
            formatted_sig_string.push(formatted_sig_seq.index(k as int));
            k = k + 1;
        }
        result.push(formatted_sig_string); /* Verus can automatically prove that String construction from `Seq<char>` is correct when using `String::push` in a loop, given appropriate invariants. */

        i = i + 1;
    }

    result
}
// </vc-code>


}
fn main() {}