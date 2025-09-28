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
/* helper modified by LLM (iteration 5): Use u64 instead of nat for executable code */
fn parse_single_format(format: &String) -> (result: FormatDescriptor)
    requires is_valid_format(*format)
    ensures result == parse_format_descriptor(*format)
{
    if format.len() == 2 {
        let c0 = format.get_char(0);
        let c1 = format.get_char(1);
        if c0 == 'f' && c1 == '8' {
            FormatDescriptor::Float64
        } else if c0 == 'f' && c1 == '4' {
            FormatDescriptor::Float32
        } else if c0 == 'i' && c1 == '4' {
            FormatDescriptor::Int32
        } else if c0 == 'i' && c1 == '8' {
            FormatDescriptor::Int64
        } else if c0 == 'S' {
            // For S followed by digit, parse the length
            let digit = (c1 as u8 - '0' as u8) as u64;
            FormatDescriptor::String(digit as nat)
        } else {
            // Default case
            FormatDescriptor::String(5 as nat)
        }
    } else if format.len() > 2 && format.get_char(0) == 'S' {
        // Handle multi-digit string lengths
        let mut len: u64 = 0;
        let mut i: usize = 1;
        while i < format.len()
            invariant
                i <= format.len(),
                1 <= i
        {
            let c = format.get_char(i);
            if '0' <= c && c <= '9' {
                len = len * 10 + (c as u8 - '0' as u8) as u64;
            }
            i = i + 1;
        }
        FormatDescriptor::String(len as nat)
    } else {
        // Default case
        FormatDescriptor::String(5 as nat)
    }
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
    /* code modified by LLM (iteration 5): Implementation remains same, issue was in helper */
    let mut fields: Vec<Field> = Vec::new();
    let mut i: usize = 0;
    
    while i < formats.len()
        invariant
            i <= formats.len(),
            fields.len() == i,
            forall|j: int| 0 <= j < i ==> fields@[j].name == names@[j],
            forall|j: int| 0 <= j < i ==> fields@[j].format == parse_format_descriptor(formats@[j]),
            match titles {
                Some(ref title_vec) => forall|j: int| 0 <= j < i ==> 
                    fields@[j].title == Some(title_vec@[j]),
                None => forall|j: int| 0 <= j < i ==> 
                    fields@[j].title.is_none(),
            }
    {
        let format_desc = parse_single_format(&formats[i]);
        let title = match &titles {
            Some(title_vec) => Some(title_vec[i].clone()),
            None => None,
        };
        let field = Field {
            name: names[i].clone(),
            format: format_desc,
            title: title,
        };
        fields.push(field);
        i = i + 1;
    }
    
    DType {
        fields: fields,
        aligned: aligned,
    }
}
// </vc-code>


}
fn main() {}