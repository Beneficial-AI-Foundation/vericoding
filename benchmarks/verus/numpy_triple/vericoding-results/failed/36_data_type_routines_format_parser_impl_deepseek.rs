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
/* helper modified by LLM (iteration 5): Fix nat usage in exec code, move to ghost context */
proof fn parse_nat_digits(s: Seq<char>) -> nat {
    if s.len() == 0 {
        0
    } else {
        let last_digit = (s[s.len() - 1] as nat) - ('0' as nat);
        parse_nat_digits(s.subrange(0, s.len() - 1)) * 10 + last_digit
    }
}

proof fn get_string_len(format: &String) -> (len: nat)
    requires is_valid_format(format@)
    ensures len == {
        if format@ == "f8".view() || format@ == "f4".view() || format@ == "i4".view() || format@ == "i8".view() {
            0
        } else {
            assert(format@.len() > 1 && format@.index(0) == 'S');
            let len_str = format@.subrange(1, format@.len());
            parse_nat_digits(len_str)
        }
    }
{
    if format@.len() > 1 && format@.index(0) == 'S' {
        let len_str = format@.subrange(1, format@.len());
        parse_nat_digits(len_str)
    } else {
        0
    }
}

proof fn format_descriptor_consistency(format: String)
    requires is_valid_format(format@)
    ensures parse_format_descriptor(format) == {
        if format@ == "f8".view() {
            FormatDescriptor::Float64
        } else if format@ == "f4".view() {
            FormatDescriptor::Float32
        } else if format@ == "i4".view() {
            FormatDescriptor::Int32
        } else if format@ == "i8".view() {
            FormatDescriptor::Int64
        } else {
            FormatDescriptor::String(get_string_len(&format))
        }
    }
{
    if format@ == "f8".view() {
    } else if format@ == "f4".view() {
    } else if format@ == "i4".view() {
    } else if format@ == "i8".view() {
    } else {
        assert(format@.len() > 1);
        assert(format@.index(0) == 'S');
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
    /* code modified by LLM (iteration 5): Use ghost context for length computation */
    let mut fields = Vec::new();
    let mut i: usize = 0;
    while i < formats.len()
        invariant
            i <= formats.len(),
            fields.len() == i,
            forall|j: int| 0 <= j < i ==> fields@[j].name == names@[j],
            forall|j: int| 0 <= j < i ==> fields@[j].format == parse_format_descriptor(formats@[j]),
            match titles {
                Some(ref title_vec) => forall|j: int| 0 <= j < i ==> fields@[j].title == Some(title_vec@[j]),
                None => forall|j: int| 0 <= j < i ==> fields@[j].title.is_none(),
            }
        decreases formats.len() - i
    {
        let format = formats.index(i);
        let name = names.index(i);
        
        let len: nat = proof {
            get_string_len(format)
        };
        
        proof {
            format_descriptor_consistency(format.clone());
        }
        
        let desc = if format@ == "f8".view() {
            FormatDescriptor::Float64
        } else if format@ == "f4".view() {
            FormatDescriptor::Float32
        } else if format@ == "i4".view() {
            FormatDescriptor::Int32
        } else if format@ == "i8".view() {
            FormatDescriptor::Int64
        } else {
            FormatDescriptor::String(len)
        };
        
        let title = match titles {
            Some(ref titles_vec) => Some(titles_vec.index(i).clone()),
            None => None,
        };
        
        let field = Field {
            name: name.clone(),
            format: desc,
            title: title,
        };
        
        fields.push(field);
        i += 1;
    }
    
    DType {
        fields: fields,
        aligned: aligned,
    }
}
// </vc-code>


}
fn main() {}