// <vc-preamble>
use vstd::prelude::*;

verus! {

/* A format descriptor for structured data types */
#[derive(Eq, PartialEq)]
pub enum FormatDescriptor {
    /* 64-bit floating point ('f8') */
    Float64,
    /* 32-bit integer ('i4') */
    Int32,
    /* Variable length string ('S5' for string of length 5) */
    String(nat),
    /* 64-bit integer ('i8') */
    Int64,
    /* 32-bit floating point ('f4') */
    Float32,
}

/* A field in a structured data type */
#[derive(Eq, PartialEq)]
pub struct Field {
    /* Field name */
    pub name: String,
    /* Format descriptor */
    pub format: FormatDescriptor,
    /* Optional title for the field */
    pub title: Option<String>,
}

/* A structured data type specification */
#[derive(Eq, PartialEq)]
pub struct DType {
    /* Vector of fields */
    pub fields: Vec<Field>,
    /* Whether fields are aligned as C-compiler would */
    pub aligned: bool,
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): runtime parser mapping to spec */
fn parse_format_descriptor_runtime(format: String) -> (result: FormatDescriptor)
    requires
        is_valid_format(format),
    ensures
        result == parse_format_descriptor(format),
{
    let res = if format@ == "f8".view() {
        FormatDescriptor::Float64
    } else if format@ == "f4".view() {
        FormatDescriptor::Float32
    } else if format@ == "i4".view() {
        FormatDescriptor::Int32
    } else if format@ == "i8".view() {
        FormatDescriptor::Int64
    } else {
        FormatDescriptor::String(5)
    };
    res
}

// </vc-helpers>

// <vc-spec>
spec fn is_valid_format(format: String) -> bool {
    format@ == "f8".view() || format@ == "f4".view() || format@ == "i4".view() || format@ == "i8".view() || 
    (format@.len() > 1 && format@.index(0) == 'S')
}

spec fn parse_format_descriptor(format: String) -> FormatDescriptor {
    if format@ == "f8".view() {
        FormatDescriptor::Float64
    } else if format@ == "f4".view() {
        FormatDescriptor::Float32
    } else if format@ == "i4".view() {
        FormatDescriptor::Int32
    } else if format@ == "i8".view() {
        FormatDescriptor::Int64
    } else {
        FormatDescriptor::String(5) // simplified for spec
    }
}

fn numpy_format_parser(
    formats: Vec<String>,
    names: Vec<String>,
    titles: Option<Vec<String>>,
    aligned: bool
) -> (result: DType)
    requires 
        formats.len() == names.len(),
        titles.is_some() ==> titles.unwrap().len() == names.len(),
        forall|i: int| 0 <= i < formats.len() ==> is_valid_format(formats@[i]),
    ensures
        result.fields.len() == formats.len(),
        forall|i: int| 0 <= i < result.fields.len() ==> result.fields@[i].name == names@[i],
        forall|i: int| 0 <= i < result.fields.len() ==> 
            result.fields@[i].format == parse_format_descriptor(formats@[i]),
        match titles {
            Some(title_vec) => forall|i: int| 0 <= i < result.fields.len() ==> 
                result.fields@[i].title == Some(title_vec@[i]),
            None => forall|i: int| 0 <= i < result.fields.len() ==> 
                result.fields@[i].title.is_none(),
        },
        result.aligned == aligned,
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): build fields vector using helper */
    let mut fields: Vec<Field> = Vec::new();
    let mut i: nat = 0;
    while i < formats.len()
        invariant
            i <= formats.len(),
            fields.len() == i,
        decreases formats.len() - i
    {
        let name_i = names[i].clone();
        let fmt_i = formats[i].clone();
        let title_i = match &titles {
            Some(tv) => Some(tv[i].clone()),
            None => None,
        };
        let desc = parse_format_descriptor_runtime(fmt_i);
        fields.push(Field { name: name_i, format: desc, title: title_i });
        i = i + 1;
    }
    DType { fields: fields, aligned: aligned }
}
// </vc-code>


}
fn main() {}