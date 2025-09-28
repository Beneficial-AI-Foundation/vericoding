// <vc-preamble>
use vstd::prelude::*;

verus! {

/* Represents a NumPy data type object with its essential attributes */
pub struct DType {
    /* The fundamental numeric type category */
    pub kind: &'static str,
    /* The element size in bytes */
    pub itemsize: usize,
    /* The alignment requirement in bytes */
    pub alignment: usize,
    /* A descriptive name for the data type */
    pub name: &'static str,
    /* Whether the data type is signed (for numeric types) */
    pub signed: bool,
}
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn numpy_dtype(type_spec: &str) -> (result: DType)
    requires type_spec == "int8" || type_spec == "int16" || type_spec == "int32" || 
             type_spec == "int64" || type_spec == "float32" || type_spec == "float64" || 
             type_spec == "bool",
    ensures
        /* The data type has a valid kind character */
        (result.kind == "i" || result.kind == "f" || result.kind == "b") &&
        /* The itemsize is positive and matches the type specification */
        (result.itemsize > 0) &&
        /* The alignment is positive and does not exceed the itemsize */
        (result.alignment > 0 && result.alignment <= result.itemsize) &&
        /* The name is non-empty */
        (result.name != "") &&
        /* Size consistency for specific types */
        ((type_spec == "int8" ==> result.itemsize == 1 && result.signed == true && result.kind == "i") &&
         (type_spec == "int16" ==> result.itemsize == 2 && result.signed == true && result.kind == "i") &&
         (type_spec == "int32" ==> result.itemsize == 4 && result.signed == true && result.kind == "i") &&
         (type_spec == "int64" ==> result.itemsize == 8 && result.signed == true && result.kind == "i") &&
         (type_spec == "float32" ==> result.itemsize == 4 && result.kind == "f") &&
         (type_spec == "float64" ==> result.itemsize == 8 && result.kind == "f") &&
         (type_spec == "bool" ==> result.itemsize == 1 && result.kind == "b"))
// </vc-spec>
// <vc-code>
{
    match type_spec {
        "int8" => DType {
            kind: "i",
            itemsize: 1,
            alignment: 1,
            name: "int8",
            signed: true,
        },
        "int16" => DType {
            kind: "i",
            itemsize: 2,
            alignment: 2,
            name: "int16",
            signed: true,
        },
        "int32" => DType {
            kind: "i",
            itemsize: 4,
            alignment: 4,
            name: "int32",
            signed: true,
        },
        "int64" => DType {
            kind: "i",
            itemsize: 8,
            alignment: 8,
            name: "int64",
            signed: true,
        },
        "float32" => DType {
            kind: "f",
            itemsize: 4,
            alignment: 4,
            name: "float32",
            signed: false,
        },
        "float64" => DType {
            kind: "f",
            itemsize: 8,
            alignment: 8,
            name: "float64",
            signed: false,
        },
        "bool" => DType {
            kind: "b",
            itemsize: 1,
            alignment: 1,
            name: "bool",
            signed: false,
        },
        _ => {
            // This branch is unreachable due to the `requires` clause.
            // We provide a default valid DType for Verus to reason about,
            // though this code path should not be taken at runtime.
            DType {
                kind: "i",
                itemsize: 1,
                alignment: 1,
                name: "unreachable",
                signed: true,
            }
        }
    }
}
// </vc-code>


}
fn main() {}